#[macro_use]
extern crate do_with_in;

use do_with_in::*;



trait Fetch<const N: usize, const WORDSIZE: usize, const OUT: usize> {
  type MEM_BLOCK;
  const MEM_SIZE: usize;
  fn fetch(&self, ip: usize) -> [u8; OUT];
}
pub struct Mem<const M: usize> {
  mem: [usize; M],
}

do_with_in!{
  sigil: $ do
  $(mk foreach
    $(let N = { $1 })
    $(let M = { $2 })
    $(if { $(logic $N < $M) } { $3 $(var x = { $(arithmetic u64u $1 + 1) $2 $3 }) $(array each foreach [ { $x } ]) } { })
  )
  $(mk mkFetch
      $(var N        = { $1 }
            WORDSIZE = { $2 })
      $(var bump     = { $(if { $(logic $(arithmetic u64u (($N * $WORDSIZE) % ((size_of u8) * 8))) = 0) } { 0 } { 1 }) } )
      $(var OUT      = { $(arithmetic usizeu (($N * $WORDSIZE) / ((size_of u8) * 8)) + $bump) })

      impl<const M: usize> Fetch<$N, $WORDSIZE, $OUT> for Mem<M> {
        type MEM_BLOCK = usize;
        const MEM_SIZE: usize = M;
      //const OUT: usize = (($N * $WORDSIZE) as usize).div_ceil(std::mem::size_of::<Self::MEM_BLOCK>()); //(N * WORDSIZE).div_ceil(std::mem::size_of::<Self::MEM_BLOCK>());
        fn fetch(&self, ip: usize) -> [u8; $OUT] {
          // We currently hardcode mem as
          // special case for when WORDSIZE = 8
          let start_big = (ip * $WORDSIZE) / std::mem::size_of::<Self::MEM_BLOCK>();
          let start_small = (ip * $WORDSIZE) % std::mem::size_of::<Self::MEM_BLOCK>();
          let end_big = ((ip + $N) * $WORDSIZE) / std::mem::size_of::<Self::MEM_BLOCK>();
          let end_small = ((ip + $N) * $WORDSIZE) % std::mem::size_of::<Self::MEM_BLOCK>();
          let num_big = ($N * $WORDSIZE) / std::mem::size_of::<Self::MEM_BLOCK>();
          let out: [u8; $OUT] = [ $(var x = {{0 $OUT (0,)}}) $(array each foreach [ $x ]) ];//*/ [0; $OUT];
          //let out: [u8; {(($N * $WORDSIZE) as usize).div_ceil(std::mem::size_of::<Self::MEM_BLOCK>())}] = core::array::from_fn(|i| {
            // There are several possibilities
            // The easy case: MEM_BLOCK = $WORDSIZE = u8
            // MEM_BLOCK > $WORDSIZE
            // MEM_BLOCK < $WORDSIZE
            // We also have to handle wrapping around when ((ip + N) * WORDSIZE) > (MEM_SIZE * MEM_BLOCK)
            // We start at start_big shifted by start_small
            //todo!()
          //}); //[0; {$N * $WORDSIZE / std::mem::size_of::<u8>()}];
          out
        }
      }
  )
  $(mkFetch 2 4)
  $(mk mem_2_4 Fetch::<2, 4, 1>::fetch(& $1, $2))
  $(mkFetch 1 4)
  $(mk mem_1_4 Fetch::<1, 4, 1>::fetch(& $1, $2))
  $(mkFetch 3 4)
  $(mk mem_3_4 Fetch::<3, 4, 2>::fetch(& $1, $2))

  const MEMLEN: usize = 2usize.pow(12);
  fn main() {
    let mut m: Mem<MEMLEN> = Mem { mem: [0usize; MEMLEN], };
    m.mem[0] = 3;
    m.mem[1] = 999;
    let ip: usize = 0;
    let q = Fetch::<2, 4, 1>::fetch(&m, ip);
    let r = $(mem_2_4 m 1);
    let s = $(mem_1_4 m 1);
    let t = $(mem_3_4 m 1);
    println!("ip = 0: {:?}", q);
    println!("ip = 1: {:?}", r);
    println!("ip = 1: {:?}", s);
    println!("ip = 1: {:?}", t);
  }

}



