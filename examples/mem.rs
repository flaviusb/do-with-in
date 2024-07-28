#[macro_use]
extern crate do_with_in;

use do_with_in::*;

do_with_in!{
  sigil: $ do

  trait Fetch<MEM_STORE_TYPE, const MEM_STORE_TYPE_SIZE: usize, const MEM_STORE_CHUNKS: usize, MEM_RETURN_TYPE, const MEM_RETURN_TYPE_SIZE: usize, const MEM_RETURN_CHUNKS: usize, const MEM_SIMULATING_TYPE_SIZE: usize, const MEM_SIMULATING_CHUNKS: usize> {
    fn fetch(&self, ip: usize) -> [MEM_RETURN_TYPE; MEM_RETURN_CHUNKS];
  }
  pub struct Mem<MEM_STORE_TYPE, const M: usize> {
    mem: [MEM_STORE_TYPE; M],
  }
  $(mk foreach
    $(var A = { $1 })
    $(var B = { $2 })
    $(var C = { $3 })
    $(var D = { [{$1 $2}] })
    $(if { $(logic $A < $B) } { $(array each $C $D) $(var x = { $(arithmetic u64u $A + 1) $B $C }) $(array each foreach [ { $x } ]) } { }))

  $(mk mkFetch
      $(var
          MEM_STORE_TYPE            = { $1 }
          MEM_STORE_TYPE_SIZE       = { $2 }
          MEM_STORE_CHUNKS          = { $3 }
          MEM_RETURN_TYPE           = { $4 }
          MEM_RETURN_TYPE_SIZE      = { $5 }
          MEM_RETURN_CHUNKS         = { $6 }
          //MEM_SIMULATING_TYPE       = { $7  }, ← needs to not be here, as it could be an impossible type like u4 or u300
          MEM_SIMULATING_TYPE_SIZE  = { $7 }
          MEM_SIMULATING_CHUNKS     = { $8 }
          fetch_wrapper             = { $9 })
      impl Fetch<$MEM_STORE_TYPE, $MEM_STORE_TYPE_SIZE, $MEM_STORE_CHUNKS, $MEM_RETURN_TYPE, $MEM_RETURN_TYPE_SIZE, $MEM_RETURN_CHUNKS, $MEM_SIMULATING_TYPE_SIZE, $MEM_SIMULATING_CHUNKS> for Mem<$MEM_STORE_TYPE, $MEM_STORE_CHUNKS> {
        fn fetch(&self, ip: usize) -> [MEM_RETURN_TYPE; MEM_RETURN_CHUNKS] { //[$MEM_RETURN_TYPE; $MEM_RETURN_CHUNKS] {
          
          let safe_ip: usize = ((ip * $MEM_SIMULATING_TYPE_SIZE) % ($MEM_STORE_TYPE_SIZE * $MEM_STORE_CHUNKS)) / $MEM_SIMULATING_TYPE_SIZE;
          $(mk bit1 // $1 is current output chunk number, $2 is the final output chunk number
                    // ip is based on MEM_SIMULATING_TYPE_SIZE, and goes out to MEM_SIMULATING_CHUNKS, wrapping around at UNDERLYING_MEM_SIZE
                   0,
            )
          $(mk bit2 // $1 is current output chunk number, $2 is the final output chunk number
                    // ip is based on MEM_SIMULATING_TYPE_SIZE, and goes out to MEM_SIMULATING_CHUNKS, wrapping around at UNDERLYING_MEM_SIZE
                    // Each cell has to check for overflow
                   0,
            )
          //if (((safe_ip as u64) + $MEM_SIMULATION_CHUNKS) * $MEM_SIMULATING_TYPE_SIZE) < ($MEM_STORE_TYPE_SIZE * $MEM_STORE_CHUNKS) {
            [  $(var x = {{0 $MEM_STORE_CHUNKS bit1}}) $(array each foreach [ $x ]) ]
          //} else {
          //  [  $(var x = {{0 $MEM_STORE_CHUNKS bit2}}) $(array each foreach [ $x ]) ]
          //}
        }
      }
      pub fn $fetch_wrapper (it: &Mem<$MEM_STORE_TYPE, $MEM_STORE_CHUNKS>, ip: usize) -> [$MEM_RETURN_TYPE; $MEM_RETURN_CHUNKS] {
        Fetch::<$MEM_STORE_TYPE, $MEM_STORE_TYPE_SIZE, $MEM_STORE_CHUNKS, $MEM_RETURN_TYPE, $MEM_RETURN_TYPE_SIZE, $MEM_RETURN_CHUNKS, $MEM_SIMULATING_TYPE_SIZE, $MEM_SIMULATING_CHUNKS>::fetch(&it, ip)
      }
    )
  $(mkFetch usize 64 256 u8 8 1 4 1 fetch_4_1)
  $(mkFetch usize 64 256 u8 8 1 4 2 fetch_4_2)
  $(mkFetch usize 64 256 u8 8 2 4 3 fetch_4_3)

}

pub fn main() {
  let mut m: Mem<usize, 256> = Mem { mem: [0usize; 256], };
  m.mem[0] = 3;
  m.mem[1] = 999;
  m.mem[2] = (1 << 63) - 1;
  m.mem[3] = (1 << 63) - 1;
  println!("ip = {}, fetching {}: {:?}", 0, 1, fetch_4_1(&m, 0));
}


/*
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
          // |mem_return| = ((size_of $mem_return_type) * 8)
          // ip and len ($N) are in terms of mem_simulating
          // $OUT is in terms of mem_return eg $(arithmetic usizeu (($N * $WORDSIZE) / ((size_of u8) * 8)) + $bump)
          // There are two lots of 5 possibilites
          // 1) |store| = |sim|,  |store| % |sim| = 0,  |sim| % |store| = 0,  |sim| < |store|,  |store| < |sim|
          // 2) |sim| = |return|, |sim| % |return| = 0, |return| % |sim| = 0, |return| < |sim|, |sim| < |return|
          //
          // $(bit ...)  should deal with 2
          // $(part ...) should deal with 1
          //
          // We also have to handle wrapping around when ((ip + N) * WORDSIZE) > (MEM_SIZE * MEM_BLOCK)
          // We start at start_big shifted by start_small
          //
          // We have start_store, start_sim, and start_return
          // And num_store, num_sim, and num_return
          // And bump_store, bump_sim, and bump_return
          //
          // get_store_from_sim n
          // for 0 block_end get_sim_from_return
          //
          // ret_ip → list of sim_ip's → list of lists of store_ip's + shifts and masks and ands
          // 
          // $(mk get_store_from_sim // $1 is the pointer in 'sim' terms
          //   $(if { $(logic $mem_store = $mem_simulate) }
          //     {
          //       self.mem[ip + $1]
          //     }
          //     {
          //     })
          // )
          // $(mk get_sim_from_return // $1 is the 'return' pointer
          //   $(if { $(logic $mem_return = $mem_simulate) }
          //     {
          //       $(array each get_store_from_sim [ {($1)} ]),
          //     }
          //     {
          //     }
          //   )
          // )
          // let out: [u8; $OUT] = [ $(var x = {{0 $OUT get_sim_from_return}}) $(array each foreach [ $x ]) ];
          $(mk part
            // start, base
            // $1 = 
            )
          $(mk bit
            // $1 = current
            // $2 = end (should correspond to $OUT) - the number of cells to generate
            // ip = base pointer
            $(if {
              $(logic $mem_simulate = $mem_return)
            } {
              // get part ip + $1, no shifts
            } {
              $(if {
                $(logic $(arithmetic u64u $mem_simulate % $mem_store) = 0)
              } {
              } {
              })
                     ((self.mem[((ip + $1) * $mem_simulate) / std::mem::size_of::<Self::MEM_BLOCK>()] << (((ip + $1) * $mem_simulate) % std::mem::size_of::<Self::MEM_BLOCK>())) & (0b11111111)) as u8
            }
            ,)
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
  $(mkFetch 1 64 4096 usize usize)
  $(mk mem_usize_usize Fetch::<4096, 1, 64, 1, usize>::fetch(& $1, $2))

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


*/
