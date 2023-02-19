use crate::util::arithmetic::{CurveAffine, FieldExt};
use std::{fmt::Debug, ops::Deref};

pub trait IntegerInstructions<F: FieldExt>: Clone + Debug {
    type Context: Debug;
    type AssignedCell: Clone + Debug;
    type AssignedInteger: Clone + Debug;

    fn assign_integer(
        &self,
        ctx: &mut Self::Context,
        integer: F, // witness
    ) -> Self::AssignedInteger;

    fn assign_constant(&self, ctx: &mut Self::Context, integer: F) -> Self::AssignedInteger;

    fn sum_with_coeff_and_const(
        &self,
        ctx: &mut Self::Context,
        values: &[(F::Scalar, impl Deref<Target = Self::AssignedInteger>)],
        constant: F::Scalar,
    ) -> Self::AssignedInteger;

    fn sum_products_with_coeff_and_const(
        &self,
        ctx: &mut Self::Context,
        values: &[(
            F::Scalar,
            impl Deref<Target = Self::AssignedInteger>,
            impl Deref<Target = Self::AssignedInteger>,
        )],
        constant: F::Scalar,
    ) -> Self::AssignedInteger;

    fn sub(
        &self,
        ctx: &mut Self::Context,
        lhs: &Self::AssignedInteger,
        rhs: &Self::AssignedInteger,
    ) -> Self::AssignedInteger;

    fn neg(&self, ctx: &mut Self::Context, value: &Self::AssignedInteger) -> Self::AssignedInteger;

    fn invert(
        &self,
        ctx: &mut Self::Context,
        value: &Self::AssignedInteger,
    ) -> Self::AssignedInteger;

    fn assert_equal(
        &self,
        ctx: &mut Self::Context,
        lhs: &Self::AssignedInteger,
        rhs: &Self::AssignedInteger,
    );
}

pub trait EccInstructions<C: CurveAffine>: Clone + Debug {
    type Context: Debug + Default;
    type ScalarChip: IntegerInstructions<
        C::Scalar,
        Context = Self::Context,
        AssignedCell = Self::AssignedCell,
        AssignedInteger = Self::AssignedScalar,
    >;
    type AssignedCell: Clone + Debug;
    type AssignedScalar: Clone + Debug;
    type AssignedEcPoint: Clone + Debug;

    fn scalar_chip(&self) -> &Self::ScalarChip;

    fn assign_constant(&self, ctx: &mut Self::Context, ec_point: C) -> Self::AssignedEcPoint;

    fn assign_point(&self, ctx: &mut Self::Context, ec_point: C) -> Self::AssignedEcPoint;

    fn sum_with_const(
        &self,
        ctx: &mut Self::Context,
        values: &[impl Deref<Target = Self::AssignedEcPoint>],
        constant: C,
    ) -> Self::AssignedEcPoint;

    fn fixed_base_msm(
        &mut self,
        ctx: &mut Self::Context,
        pairs: &[(impl Deref<Target = Self::AssignedScalar>, C)],
    ) -> Self::AssignedEcPoint;

    fn variable_base_msm(
        &mut self,
        ctx: &mut Self::Context,
        pairs: &[(
            impl Deref<Target = Self::AssignedScalar>,
            impl Deref<Target = Self::AssignedEcPoint>,
        )],
    ) -> Self::AssignedEcPoint;

    fn assert_equal(
        &self,
        ctx: &mut Self::Context,
        lhs: &Self::AssignedEcPoint,
        rhs: &Self::AssignedEcPoint,
    );
}

mod halo2_lib {
    use crate::halo2_proofs::halo2curves::CurveAffineExt;
    use crate::{
        loader::halo2::{EccInstructions, IntegerInstructions},
        util::arithmetic::{CurveAffine, Field},
    };
    use halo2_base::{
        self,
        gates::{builder::GateThreadBuilder, GateChip, GateInstructions, RangeInstructions},
        AssignedValue,
        QuantumCell::{Constant, Existing},
    };
    use halo2_ecc::{
        bigint::CRTInteger,
        ecc::{fixed_base::FixedEcPoint, BaseFieldEccChip, EcPoint},
        fields::{FieldChip, PrimeField},
    };
    use std::{ops::Deref, sync::Mutex};

    type AssignedInteger<C> = CRTInteger<<C as CurveAffine>::ScalarExt>;
    type AssignedEcPoint<C> = EcPoint<<C as CurveAffine>::ScalarExt, AssignedInteger<C>>;

    impl<F: PrimeField> IntegerInstructions<F> for GateChip<F> {
        type Context = GateThreadBuilder<F>;
        type AssignedCell = AssignedValue<F>;
        type AssignedInteger = AssignedValue<F>;

        fn assign_integer(&self, ctx: &mut Self::Context, integer: F) -> Self::AssignedInteger {
            ctx.main(0).load_witness(integer)
        }

        fn assign_constant(&self, ctx: &mut Self::Context, integer: F) -> Self::AssignedInteger {
            ctx.main(0).load_constant(integer)
        }

        fn sum_with_coeff_and_const(
            &self,
            ctx: &mut Self::Context,
            values: &[(F::Scalar, impl Deref<Target = Self::AssignedInteger>)],
            constant: F,
        ) -> Self::AssignedInteger {
            let mut a = Vec::with_capacity(values.len() + 1);
            let mut b = Vec::with_capacity(values.len() + 1);
            if constant != F::zero() {
                a.push(Constant(constant));
                b.push(Constant(F::one()));
            }
            a.extend(values.iter().map(|(_, a)| Existing(*a.deref())));
            b.extend(values.iter().map(|(c, _)| Constant(*c)));
            self.inner_product(ctx.main(0), a, b)
        }

        fn sum_products_with_coeff_and_const(
            &self,
            ctx: &mut Self::Context,
            values: &[(
                F::Scalar,
                impl Deref<Target = Self::AssignedInteger>,
                impl Deref<Target = Self::AssignedInteger>,
            )],
            constant: F,
        ) -> Self::AssignedInteger {
            match values.len() {
                0 => ctx.main(0).load_constant(constant),
                _ => self.sum_products_with_coeff_and_var(
                    ctx.main(0),
                    values.iter().map(|(c, a, b)| (*c, Existing(*a.deref()), Existing(*b.deref()))),
                    Constant(constant),
                ),
            }
        }

        fn sub(
            &self,
            ctx: &mut Self::Context,
            a: &Self::AssignedInteger,
            b: &Self::AssignedInteger,
        ) -> Self::AssignedInteger {
            GateInstructions::sub(self, ctx.main(0), Existing(*a), Existing(*b))
        }

        fn neg(&self, ctx: &mut Self::Context, a: &Self::AssignedInteger) -> Self::AssignedInteger {
            GateInstructions::neg(self, ctx.main(0), Existing(*a))
        }

        fn invert(
            &self,
            ctx: &mut Self::Context,
            a: &Self::AssignedInteger,
        ) -> Self::AssignedInteger {
            // make sure scalar != 0
            let is_zero = self.is_zero(ctx.main(0), *a);
            self.assert_is_const(ctx.main(0), &is_zero, &F::zero());
            GateInstructions::div_unsafe(self, ctx.main(0), Constant(F::one()), Existing(*a))
        }

        fn assert_equal(
            &self,
            ctx: &mut Self::Context,
            a: &Self::AssignedInteger,
            b: &Self::AssignedInteger,
        ) {
            ctx.main(0).constrain_equal(a, b);
        }
    }

    impl<'chip, C: CurveAffineExt> EccInstructions<C> for BaseFieldEccChip<'chip, C>
    where
        C::ScalarExt: PrimeField,
        C::Base: PrimeField,
    {
        type Context = GateThreadBuilder<C::Scalar>;
        type ScalarChip = GateChip<C::Scalar>;
        type AssignedCell = AssignedValue<C::Scalar>;
        type AssignedScalar = AssignedValue<C::Scalar>;
        type AssignedEcPoint = AssignedEcPoint<C>;

        fn scalar_chip(&self) -> &Self::ScalarChip {
            self.field_chip.range().gate()
        }

        fn assign_constant(&self, ctx: &mut Self::Context, point: C) -> Self::AssignedEcPoint {
            let fixed = FixedEcPoint::<C::Scalar, C>::from_curve(
                point,
                self.field_chip.num_limbs,
                self.field_chip.limb_bits,
            );
            FixedEcPoint::assign(fixed, self.field_chip(), ctx.main(0))
        }

        fn assign_point(&self, ctx: &mut Self::Context, point: C) -> Self::AssignedEcPoint {
            let assigned = self.assign_point(ctx.main(0), point);
            let is_valid = self.is_on_curve_or_infinity::<C>(ctx.main(0), &assigned);
            self.field_chip().gate().assert_is_const(ctx.main(0), &is_valid, &C::Scalar::one());
            assigned
        }

        fn sum_with_const(
            &self,
            ctx: &mut Self::Context,
            values: &[impl Deref<Target = Self::AssignedEcPoint>],
            constant: C,
        ) -> Self::AssignedEcPoint {
            let constant = if bool::from(constant.is_identity()) {
                None
            } else {
                let constant = EccInstructions::<C>::assign_constant(self, ctx, constant);
                Some(constant)
            };
            self.sum::<C>(ctx.main(0), constant.iter().chain(values.iter().map(Deref::deref)))
        }

        fn variable_base_msm(
            &mut self,
            ctx: &mut Self::Context,
            pairs: &[(
                impl Deref<Target = Self::AssignedScalar>,
                impl Deref<Target = Self::AssignedEcPoint>,
            )],
        ) -> Self::AssignedEcPoint {
            let (scalars, points): (Vec<_>, Vec<_>) = pairs
                .iter()
                .map(|(scalar, point)| (vec![*scalar.deref()], point.deref().clone()))
                .unzip();
            let thread_pool = Mutex::new(std::mem::take(ctx));
            let res = BaseFieldEccChip::<C>::variable_base_msm::<C>(
                self,
                &thread_pool,
                &points,
                scalars,
                C::Scalar::NUM_BITS as usize,
            );
            *ctx = thread_pool.into_inner().unwrap();
            res
        }

        fn fixed_base_msm(
            &mut self,
            ctx: &mut Self::Context,
            pairs: &[(impl Deref<Target = Self::AssignedScalar>, C)],
        ) -> Self::AssignedEcPoint {
            let (scalars, points): (Vec<_>, Vec<_>) = pairs
                .iter()
                .filter_map(|(scalar, point)| {
                    if point.is_identity().into() {
                        None
                    } else {
                        Some((vec![*scalar.deref()], *point))
                    }
                })
                .unzip();
            let thread_pool = Mutex::new(std::mem::take(ctx));
            let res = BaseFieldEccChip::<C>::fixed_base_msm::<C>(
                self,
                &thread_pool,
                &points,
                scalars,
                C::Scalar::NUM_BITS as usize,
            );
            *ctx = thread_pool.into_inner().unwrap();
            res
        }

        fn assert_equal(
            &self,
            ctx: &mut Self::Context,
            a: &Self::AssignedEcPoint,
            b: &Self::AssignedEcPoint,
        ) {
            self.assert_equal(ctx.main(0), a, b);
        }
    }
}
