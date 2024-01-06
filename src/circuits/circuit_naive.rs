use halo2_proofs::{
    arithmetic::Field,
    circuit::{AssignedCell, Cell, Layouter, SimpleFloorPlanner, Value},
    poly::{Rotation},
    plonk::{
        Advice, ConstraintSystem, Circuit, 
        Column, Fixed, Any, Error,
        Selector, Expression,
        VirtualCells,
    },
};
use std::marker::PhantomData;

/*
@note

•   We want to construct circuits encoding the constraints associated with the following claim: 
    that we know x, y, z, k such that f(0) = x, f(1) = y, f(k) = z.

•   Many tutorials for the Fibonacci circuit leave k and z public, but it's easy to 
    recover all the private values in this circuit by knowing these two numbers.
    Since this defeats the purpose of hiding the values in the circuit wires, 
    it makes sense to keep z private (advice region) and k public (instance region) instead.
•   
•   This is what the naive table for the fib circuit would look like
•   if one were trying to prove that, given f(0) = 1 and f(1) = 1, 
•   f(9) = 55.
•   
•   note how one would need to enforce copy constraints between c_i and b_i+1
•   as the output of the current gate will be an input into the next gate.

    a | b | c | z | s | i
    ----------------------
    1   1   2   55  1   7
    1   2   3   55  1   
    2   3   5   55  1   
    3   5   8   55  1
    5   8   13  55  1

•   A better version only puts f(k-2), f(k-1), and z in the table.

*/

/*
@note
•   We need a single chip for this circuit.
•   Every chip has its own table apparently
*/
#[derive(Clone, Debug)]
pub struct FibConfig{
    advice: [Column<Advice>; 3],
    selector: Selector,
}

/*
@note
•   We have a PhantomData as a field of this struct
    to influence the drop order of things (aka if this 
    value needs to be dropped then other F's might need
    to get dropped too)
*/
struct FibChip<F: Field>{
    config: FibConfig,
    _marker: PhantomData<F>,
}

impl<F: Field> FibChip<F>{
    //set chip config (what table it uses)
    fn construct(cnfg: FibConfig) -> Self{
        Self{
            config: cnfg,
            _marker: PhantomData 
        }
    }

    fn configure(
        cs: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 3],
    ) -> FibConfig {
        let col_a: Column<Advice> = advice[0];
        let col_b: Column<Advice> = advice[1];
        let col_c: Column<Advice> = advice[2];
        let selector: Selector = cs.selector();
        cs.enable_equality(col_a);
        cs.enable_equality(col_b);
        cs.enable_equality(col_c);
        /*
        @note
        •   the closure here creates the gate that uses the input
            from the advice columns to enforce the recursion constraints

        •   Rotation::cur() and Rotation::next() control the positions relative to
            the CURRENT REGION from which inputs/outputs to the constraints are chosen
        
        •   In every row of the advice region, we must have that a_i + b_i - c_i = 0
        */
        cs.create_gate("add", |cs: &mut VirtualCells<'_, F>| {           
            //get expressions from values in table
            let s: Expression<F> = cs.query_selector(selector);

            //fib_n
            let a: Expression<F> = cs.query_advice(col_a, Rotation::cur());

            //fib_n+1
            let b: Expression<F> = cs.query_advice(col_b, Rotation::cur());

            //fib_n+2
            let c: Expression<F> = cs.query_advice(col_c, Rotation::cur());

            //if selected, require that f_n + f_n+1 - f_n+2 = 0
            vec![s*(a + b - c)]
        });
        FibConfig{
            advice: [col_a, col_b, col_c],
            selector: selector,
        }
    }

    /*
    @todo
    •   Should break this down
    •   Assign first row of advice (x, y, z)
    •   Assign first row of instance (just k)
    */
    fn assign_row(
        &self, 
        mut layouter: impl Layouter<F>, 
        a: Value<F>, 
        b: Value<F>, 
        copy_cell: Option<AssignedCell<F, F>>,
        z: Value<F>,
        is_last: bool,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        //assign input a to region
        layouter.assign_region(
            || "first_row", //annotation
            |mut region| { //assignment 
                self.config.selector.enable(&mut region, 0)?;
                /*
                @note
                •   Assign private values f_0, f_1, f_2 in the first advice row.
                •   Note that the only public variable here is the index of the term
                    to check. 
                */
                let a_cell = region.assign_advice(
                    || "f_0", //annotation
                    self.config.advice[0], //column
                    0, //offset
                    || a //closure which outputs the value to assign
                )?;
                
                let b_cell = if let Some(cc) = &copy_cell {
                    cc.copy_advice(
                        || "current result = prev input", //annotation
                        &mut region, //region,
                        self.config.advice[1], //column
                        0, //offset
                    )?
                } else {
                    region.assign_advice(
                        || "f_1",  //annotation
                        self.config.advice[1], //column
                        0, //offset
                        || b //closure which outputs the value to assign
                    )?
                };

                /*
                @note
                •   In the last row, we need to check that f(k) = f(k-1) + f(k-2) = z.
                •   We can do this by putting z in the cell instead of a + b
                */
                let c_cell = region.assign_advice(
                    || "f_2",  //annotation
                    self.config.advice[2], //column
                    0, //offset
                    || if !is_last {
                        a_cell.value().copied() + b_cell.value()
                    } else{
                        z
                    }
                )?;

                Ok((a_cell, b_cell, c_cell))
            }
        )
    }
}

#[derive(Default)]
struct FibCircuit<F: Field>{
    //inputs to this circuit
    pub a: Value<F>,
    pub b: Value<F>,
    pub k: Value<usize>,
    pub z: Value<F>,
}

impl<F: Field> Circuit<F> for FibCircuit<F>{
    type Config = FibConfig;
    type FloorPlanner = SimpleFloorPlanner;
    
    fn without_witnesses(&self) -> Self{
        Self::default()
    }

    fn configure(cs: &mut ConstraintSystem<F>) -> Self::Config {
        //instantiate advice columns
        let col_a = cs.advice_column();
        let col_b = cs.advice_column();
        let col_c = cs.advice_column();
        FibChip::configure(cs, [col_a, col_b, col_c])
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error>{
        //create chip
        let fib_chip: FibChip<F> = FibChip::construct(config);
        let mut fib0 = self.a;
        let mut fib1 = self.b;
        let mut fibtemp = self.b;
        
        //@note constrain first cell of instance col to equal k
        
        //layouter.constrain_instance(k_cell.cell(), self.config.instance, 0);
        let mut copy_cell: Option<AssignedCell<F, F>> = None;
        //@note since we get f(2) in the first row, we need k-1 iterations [0, v-1)
        let result = self.k.map(|v| {
            (0..v-1).for_each(|x| {
                let (a_cell, b_cell, c_cell) = fib_chip.assign_row(
                    layouter.namespace(||format!("assign f_{}, f_{}, f_{}", x, x+1, x+2)),
                    fib0,
                    fib1,
                    copy_cell.clone(),
                    self.z,
                    x == v-2
                ).unwrap();
                copy_cell = Some(c_cell);
                fibtemp = fib1;
                fib1 = fib0 + &fibtemp;
                fib0 = fibtemp;
            });
        });
        Ok(())
    }
}

#[cfg(test)]
mod tests{
    use super::*;
    use halo2_proofs::{circuit::SimpleFloorPlanner, pasta::Fp, dev::MockProver};

    #[test]
    fn test_complete(){
        let test_a = Fp::from(1);
        let test_b = Fp::from(2);
        let test_k = 9_usize;
        let test_z = Fp::from(89);

        let circ = FibCircuit{
            a: Value::<Fp>::known(test_a),
            b: Value::<Fp>::known(test_b),
            k: Value::<usize>::known(test_k),
            z: Value::<Fp>::known(test_z),
        };

        let prover = MockProver::run(8, &circ, vec![]).unwrap();

        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    #[should_panic]
    fn test_sound(){
        let test_a = Fp::from(5);
        let test_b = Fp::from(8);
        let test_k = 11_usize;
        let test_z = Fp::from(55);

        let circ = FibCircuit{
            a: Value::<Fp>::known(test_a),
            b: Value::<Fp>::known(test_b),
            k: Value::<usize>::known(test_k),
            z: Value::<Fp>::known(test_z),
        };

        let prover = MockProver::run(8, &circ, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
    
}