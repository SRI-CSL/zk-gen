use ark_bn254::{Fr};
use ark_ff::{
    biginteger::BigInteger256 as BigInteger,
    fields::{FftParameters, Fp64, Fp256, Fp256Parameters, FpParameters, Fp64Parameters},
};

pub type Field = Fr;
/*
pub type Fr = Fp256<FrParameters>;

pub struct FrParameters;

impl Fp256Parameters for FrParameters {}
impl FftParameters for FrParameters {
    type BigInt = BigInteger;

    const TWO_ADICITY: u32 = 28;

    #[rustfmt::skip]
    const TWO_ADIC_ROOT_OF_UNITY: BigInteger = BigInteger([
	0x2a3c09f0a58a7e85,
	0x00e0a7eb8ef62abc,
	0x402d111e41112ed4,
	0x9bd61b6e725b19f0
    ]);
}
impl FpParameters for FrParameters {
    #[rustfmt::skip]
    const MODULUS: BigInteger = BigInteger([
	0x30644e72e131a029,
	0xb85045b68181585d,
	0x2833e84879b97091,
	0x43e1f593f0000001
    ]);

    const MODULUS_BITS: u32 = 254;

    const CAPACITY: u32 = Self::MODULUS_BITS - 1;

    const REPR_SHAVE_BITS: u32 = 1; //?

    #[rustfmt::skip]
    //multiplicative identity of field
    
    const R: BigInteger = BigInteger([
	0x1a0941358a12fadc,
	0xf2917c7a1b589269,
	0x35a9954bc031e0a6,
	0x77297dc392126f1
    ]);

    #[rustfmt::skip]
    const R2: BigInteger = BigInteger([
	0x0000000000000000,
	0x0000000000000000,
	0x0000000000000000,
	0x00000000000000010
    ]);

    const INV: u64 = 0xc2e1f593efffffff;

    /// GENERATOR = 7
    /// Encoded in Montgomery form, so the value here is
    /// 7 * R % q = 24006497034320510773280787438025867407531605151569380937148207556313189711857
    #[rustfmt::skip]
    const GENERATOR: BigInteger = BigInteger([
	0x0000000000000000, 
    	0x0000000000000000, 
    	0x0000000000000000, 
	0x0000000000000005
    ]);

    #[rustfmt::skip]
    const MODULUS_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
	0x183227397098d014,
	0xdc2822db40c0ac2e,
	0x9419f4243cdcb848,
	0xa1f0fac9f8000000

    ]);

    // T and T_MINUS_ONE_DIV_TWO, where MODULUS - 1 = 2^S * T
    // For T coprime to 2

    // T = (MODULUS - 1) / 2^S =
    // 12208678567578594777604504606729831043093128246378069236549469339647
    #[rustfmt::skip]
    const T: BigInteger = BigInteger([
	0x30644e72e131a029,
	0xb85045b68181585d,
	0x2833e84879b97091,
	0x43e1f593f

    ]);

    // (T - 1) / 2 =
    // 6104339283789297388802252303364915521546564123189034618274734669823
    #[rustfmt::skip]
    const T_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
	0x183227397098d014,
	0xdc2822db40c0ac2e,
	0x9419f4243cdcb848,
	0xa1f0fac9f
    ]);
}
#[test]
fn test_field_ops(){
    let one = Fr::from(1u32);
    let two = Fr::from(3u32);
    assert_eq!(one + two, two + one);
    assert_eq!(two / one, two);
}
*/
