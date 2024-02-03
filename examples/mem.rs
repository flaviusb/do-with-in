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
    $(if { $(logic $N < $M) } { $(array each $3 [{$1 $2}]) $(var x = { $(arithmetic u64u $1 + 1) $2 $3 }) $(array each foreach [ { $x } ]) } { })
  )
  $(mk mkFetch
      $(var N        = { $1 }
            WORDSIZE = { $2 })
      $(var bump     = { $(if { $(logic $(arithmetic u64u (($N * $WORDSIZE) % ((size_of u8) * 8))) = 0) } { 0 } { 1 }) } )
      $(var OUT      = { $(arithmetic usizeu (($N * $WORDSIZE) / ((size_of u8) * 8)) + $bump) })

      impl<const M: usize> Fetch<$N, $WORDSIZE, $OUT> for Mem<M> {
        type MEM_BLOCK = usize;
        const MEM_SIZE: usize = M;
        fn fetch(&self, ip: usize) -> [u8; $OUT] {
          // We currently hardcode mem as u8
          // There are several possibilities
          // The easy case: MEM_BLOCK = $WORDSIZE = u8
          // MEM_BLOCK > $WORDSIZE
          // MEM_BLOCK < $WORDSIZE
          // We also have to handle wrapping around when ((ip + N) * WORDSIZE) > (MEM_SIZE * MEM_BLOCK)
          // We start at start_big shifted by start_small
          $(mk bit ((self.mem[((ip + $1) * $WORDSIZE) / std::mem::size_of::<Self::MEM_BLOCK>()] << (((ip + $1) * $WORDSIZE) % std::mem::size_of::<Self::MEM_BLOCK>())) & (0b11111111)) as u8,)
          let out: [u8; $OUT] = [ $(var x = {{0 $OUT bit}}) $(array each foreach [ $x ]) ];
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
  $(mkFetch 4 12)
  $(mk mem_4_12 Fetch::<4, 12, 6>::fetch(& $1, $2))

  const MEMLEN: usize = 2usize.pow(12);
  fn main() {
    let mut m: Mem<MEMLEN> = Mem { mem: [0usize; MEMLEN], };
    m.mem[0] = 3;
    m.mem[1] = 999;
    m.mem[2] = (1 << 63) - 1;
    m.mem[3] = (1 << 63) - 1;
    let ip: usize = 0;
    let q = Fetch::<2, 4, 1>::fetch(&m, ip);
    let r = $(mem_2_4 m 1);
    let s = $(mem_1_4 m 1);
    let t = $(mem_3_4 m 1);
    let u = $(mem_4_12 m 0);
    let v = $(mem_4_12 m 1);
    let w = $(mem_4_12 m 2);
    let y = $(mem_4_12 m 3);
    let z = $(mem_4_12 m 4);
    println!("ip = 0: {:?}", q);
    println!("ip = 1: {:?}", r);
    println!("ip = 1: {:?}", s);
    println!("ip = 1: {:?}", t);
    println!("ip = 0: {:?}", u);
    println!("ip = 1: {:?}", v);
    println!("ip = 2: {:?}", w);
    println!("ip = 3: {:?}", y);
    println!("ip = 4: {:?}", z);
  }

}



