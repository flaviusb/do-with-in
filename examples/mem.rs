#[macro_use]
extern crate do_with_in;

use do_with_in::*;



trait Fetch<const MEM_STORE_SIZE: usize, const N: usize, const WORDSIZE: usize, const OUT: usize, OUT_CHUNKS> {
  type MEM_BLOCK;
  const MEM_SIZE: usize;
  fn fetch(&self, ip: usize) -> [OUT_CHUNKS; OUT];
}
pub struct Mem<const M: usize> {
  mem: [usize; M],
}

do_with_in!{
  sigil: $ do
  $(mk foreach
    $(var A = { $1 })
    $(var B = { $2 })
    $(var C = { $3 })
    $(var D = { [{$1 $2}] })
    $(if { $(logic $A < $B) } { $(array each $C $D) $(var x = { $(arithmetic u64u $A + 1) $B $C }) $(array each foreach [ { $x } ]) } { })
  )
  $(mk case
    $(var ret = { $3 })
    $(var insert = { { $2 } })
    $(let rep = { {$(if 
                            {$(logic eq_str $1 $(array ith get 0 $test))}
                            {
                              $(var ret = { $(array ith get 1 $test) } )
                            }
                            {}
                            )} } ) 
    $(array map false test $rep $insert)
    $ret
    )
  $(mk ok_mask
    $(var n = { $(naiveStringifier $1) })
    $(var x = { $(array each case [{$n [{[{"u8"} {255}]} {[{"u16"} {65535}]} {[{"u32"} {4294967295}]} {[{"u64"} {18446744073709551615}]} ] }]) })
    $(var y = {$(arithmetic usizeu ((size_of $1) * 8))})
    $(array each arithmetic [{$1 $x < ($y - $2)}]))
  $(mk mkFetch
      $(var N            = { $1 }
            WORDSIZE     = { $2 }
            mem_store_capacity = { $3 }
            mem_store_type     = { $4 }
            mem_return_type    = { $5 }
            )
      $(var
            mem_store    = { $(arithmetic u64u ((size_of $mem_store_type) * 8)) }
            mem_return   = { $(arithmetic u64u ((size_of $mem_return_type) * 8)) }
            mem_simulate = { $2 }
            )
      $(var bump       = { $(if { $(logic $(arithmetic u64u (($N * $mem_simulate) % $mem_return)) = 0) } { 0 } { 1 }) } )
      $(var OUT        = { $(arithmetic usizeu (($N * $mem_simulate) / $mem_return) + $bump) })

      impl Fetch<$mem_store_capacity, $N, $mem_simulate, $OUT, $mem_return_type> for Mem<$mem_store_capacity> {
        type MEM_BLOCK = $mem_store_type;
        const MEM_SIZE: usize = $mem_store_capacity;
        fn fetch(&self, ip: usize) -> [$mem_return_type; $OUT] {
          // We have mem_store, mem_return, and mem_simulating as three binary container types
          // We currently hardcode mem_return as u8, so |mem_return| = ((size_of u8) * 8)
          // ip and len ($N) are in terms of mem_simulating
          // $OUT is in terms of mem_return eg $(arithmetic usizeu (($N * $WORDSIZE) / ((size_of u8) * 8)) + $bump)
          // There are two lots of 5 possibilites
          // 1) |store| = |sim|,  |store| % |sim| = 0,  |sim| % |store| = 0,  |sim| < |store|,  |store| < |sim|
          // 2) |sim| = |return|, |sim| % |return| = 0, |return| % |sim| = 0, |return| < |sim|, |sim| < |return|
          //
          // $(bit ...)  should deal with 1
          // $(part ...) should deal with 2
          //
          // We also have to handle wrapping around when ((ip + N) * WORDSIZE) > (MEM_SIZE * MEM_BLOCK)
          // We start at start_big shifted by start_small
          $(mk part
            // start, base
            )
          $(mk bit ((self.mem[((ip + $1) * $mem_simulate) / std::mem::size_of::<Self::MEM_BLOCK>()] << (((ip + $1) * $mem_simulate) % std::mem::size_of::<Self::MEM_BLOCK>())) & (0b11111111)) as u8,)
          let out: [u8; $OUT] = [ $(var x = {{0 $OUT bit}}) $(array each foreach [ $x ]) ];
          out
        }
      }
  )
  $(mkFetch 2 4 4096 usize u8)
  $(mk mem_2_4 Fetch::<4096, 2, 4, 1, u8>::fetch(& $1, $2))
  $(mkFetch 1 4 4096 usize u8)
  $(mk mem_1_4 Fetch::<4096, 1, 4, 1, u8>::fetch(& $1, $2))
  $(mkFetch 3 4 4096 usize u8)
  $(mk mem_3_4 Fetch::<4096, 3, 4, 2, u8>::fetch(& $1, $2))
  $(mkFetch 4 12 4096 usize u8)
  $(mk mem_4_12 Fetch::<4096, 4, 12, 6, u8>::fetch(& $1, $2))

  const MEMLEN: usize = 2usize.pow(12);
  fn main() {
    println!("bitmasks: {} {:#b}, {} {:#b}, {} {:#b}, {} {:#b}.", 1, $(ok_mask u8 1), 3, $(ok_mask u8 3), 14, $(ok_mask u16 14), 7, $(ok_mask u8 7));
    println!("bitmasks and shifts: {} {} {:#b}, {} {} {:#b}, {} {} {:#b}, {} {} {:#b}.", 1, 1, $(arithmetic u8 $(ok_mask u8 1) > 1), 3, 3, $(arithmetic u8 $(ok_mask u8 3) > 3), 14, 1, $(arithmetic u16 $(ok_mask u16 14) > 1), 7, 17, $(arithmetic u64 $(ok_mask u64 7) > 17));
    let fff = $(case "u8" [ { [{"u8"} {255}] } { [{"u16"} {65535}] } { [{"u32"} {4294967295}] } { [{"u64"} {18446744073709551615}] } ] 3);
    println!("wafawef: {}", fff);
    let mut m: Mem<MEMLEN> = Mem { mem: [0usize; MEMLEN], };
    m.mem[0] = 3;
    m.mem[1] = 999;
    m.mem[2] = (1 << 63) - 1;
    m.mem[3] = (1 << 63) - 1;
    let ip: usize = 0;
    let q = Fetch::<4096, 2, 4, 1, u8>::fetch(&m, ip);
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
    println!("ip =  1: {:?}", v);
    println!("ip =  2: {:?}", w);
    println!("ip =  3: {:?}", y);
    println!("ip =  4: {:?}", z);
    println!("ip =  {}: {:?}", 5, $(mem_4_12 m  5));
    println!("ip =  {}: {:?}", 6, $(mem_4_12 m  6));
    println!("ip =  {}: {:?}", 7, $(mem_4_12 m  7));
    println!("ip =  {}: {:?}", 8, $(mem_4_12 m  8));
    println!("ip =  {}: {:?}", 9, $(mem_4_12 m  9));
    println!("ip = {}: {:?}", 10, $(mem_4_12 m 10));
    println!("ip = {}: {:?}", 11, $(mem_4_12 m 11));
    println!("ip = {}: {:?}", 12, $(mem_4_12 m 12));
    println!("ip = {}: {:?}", 13, $(mem_4_12 m 13));
    println!("ip = {}: {:?}", 14, $(mem_4_12 m 14));
    println!("ip = {}: {:?}", 15, $(mem_4_12 m 15));
    println!("ip = {}: {:?}", 16, $(mem_4_12 m 16));
    println!("ip = {}: {:?}", 17, $(mem_4_12 m 17));
    println!("ip = {}: {:?}", 18, $(mem_4_12 m 18));
    println!("ip = {}: {:?}", 19, $(mem_4_12 m 19));
    println!("ip = {}: {:?}", 20, $(mem_4_12 m 20));
    println!("ip = {}: {:?}", 21, $(mem_4_12 m 21));
    println!("ip = {}: {:?}", 22, $(mem_4_12 m 22));
  }

}



