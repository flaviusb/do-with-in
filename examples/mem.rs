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
          MEM_SIMULATING_TYPE_SIZE  = { $7 }
          MEM_SIMULATING_CHUNKS     = { $8 }
          fetch_wrapper             = { $9 })
      impl Fetch<$MEM_STORE_TYPE, $MEM_STORE_TYPE_SIZE, $MEM_STORE_CHUNKS, $MEM_RETURN_TYPE, $MEM_RETURN_TYPE_SIZE, $MEM_RETURN_CHUNKS, $MEM_SIMULATING_TYPE_SIZE, $MEM_SIMULATING_CHUNKS> for Mem<$MEM_STORE_TYPE, $MEM_STORE_CHUNKS> {
        fn fetch(&self, ip: usize) -> [$MEM_RETURN_TYPE; $MEM_RETURN_CHUNKS] {
          
          let safe_ip: usize = ((ip * $MEM_SIMULATING_TYPE_SIZE) % ($MEM_STORE_TYPE_SIZE * $MEM_STORE_CHUNKS)) / $MEM_SIMULATING_TYPE_SIZE;
          $(mk bit1 // $1 is current output chunk number, $2 is the final output chunk number
                    // ip is based on MEM_SIMULATING_TYPE_SIZE, and goes out to MEM_SIMULATING_CHUNKS, wrapping around at UNDERLYING_MEM_SIZE
                    // To work out which chunk the first bit is in, we do ((ip + $1) * $MEM_SIMULATING_TYPE_SIZE / $MEM_STORE_TYPE_SIZE) as usize
                    // To work out how far through the first chunk the first bit is, we do ((ip + $1) * $MEM_SIMULATING_TYPE_SIZE % $MEM_STORE_TYPE_SIZE)
                    // To work out how many chunks it occupies, we do ((((ip + $1) * $MEM_SIMULATING_TYPE_SIZE / $MEM_STORE_TYPE_SIZE) + (($MEM_SIMULATING_TYPE_SIZE - 1) / $MEM_STORE_TYPE_SIZE)) as usize) - (((ip + $1) * $MEM_SIMULATING_TYPE_SIZE / $MEM_STORE_TYPE_SIZE) as usize)
                   ((self.mem[((ip + $1) * $MEM_SIMULATING_TYPE_SIZE) / $MEM_STORE_TYPE_SIZE]) >> (((ip + $1) * $MEM_SIMULATING_TYPE_SIZE) % $MEM_STORE_TYPE_SIZE)) as $MEM_RETURN_TYPE,
            )
          $(mk bit2 // $1 is current output chunk number, $2 is the final output chunk number
                    // ip is based on MEM_SIMULATING_TYPE_SIZE, and goes out to MEM_SIMULATING_CHUNKS, wrapping around at UNDERLYING_MEM_SIZE
                    // Each cell has to check for overflow
                   0,
            )
          if (((safe_ip as u64) + $MEM_SIMULATING_CHUNKS) * $MEM_SIMULATING_TYPE_SIZE) < ($MEM_STORE_TYPE_SIZE * $MEM_STORE_CHUNKS) {
            [  $(var x = {{0 $MEM_RETURN_CHUNKS bit1}}) $(array each foreach [ $x ]) ]
          } else {
            [  $(var x = {{0 $MEM_RETURN_CHUNKS bit2}}) $(array each foreach [ $x ]) ]
          }
        }
      }
      pub fn $fetch_wrapper (it: &Mem<$MEM_STORE_TYPE, $MEM_STORE_CHUNKS>, ip: usize) -> [$MEM_RETURN_TYPE; $MEM_RETURN_CHUNKS] {
        Fetch::<$MEM_STORE_TYPE, $MEM_STORE_TYPE_SIZE, $MEM_STORE_CHUNKS, $MEM_RETURN_TYPE, $MEM_RETURN_TYPE_SIZE, $MEM_RETURN_CHUNKS, $MEM_SIMULATING_TYPE_SIZE, $MEM_SIMULATING_CHUNKS>::fetch(it, ip)
      }
    )
  $(mkFetch usize 64 256 u8 8 1 4 1 fetch_4_1)
  $(mkFetch usize 64 256 u8 8 1 4 2 fetch_4_2)
  $(mkFetch usize 64 256 u8 8 2 4 3 fetch_4_3)
  $(mkFetch usize 64 256 u8 8 2 9 1 fetch_9_1)
  $(mkFetch usize 64 256 u8 8 3 9 2 fetch_9_2)
  $(mkFetch usize 64 256 u8 8 4 9 3 fetch_9_3)

}

pub fn main() {
  let mut m: Mem<usize, 256> = Mem { mem: [0usize; 256], };
  m.mem[0] = 0b1010_1111_1010_0101_1100_1010_0011_1111;
  m.mem[1] = 999;
  m.mem[2] = (1 << 63) - 1;
  m.mem[3] = (1 << 63) - 1;
  println!("ip = {}, fetching {}{}: {:?}{}",  0, 1, "u4", fetch_4_1(&m, 0),  "u8");
  println!("ip = {}, fetching {}{}: {:?}{}",  0, 2, "u4", fetch_4_2(&m, 0),  "u8");
  println!("ip = {}, fetching {}{}: {:?}{}",  0, 3, "u4", fetch_4_3(&m, 0),  "u8");
  println!("ip = {}, fetching {}{}: {:?}{}",  1, 1, "u4", fetch_4_1(&m, 1),  "u8");
  println!("ip = {}, fetching {}{}: {:?}{}",  1, 2, "u4", fetch_4_2(&m, 1),  "u8");
  println!("ip = {}, fetching {}{}: {:?}{}",  1, 3, "u4", fetch_4_3(&m, 1),  "u8");
  println!("ip = {}, fetching {}{}: {:?}{}",  2, 1, "u4", fetch_4_1(&m, 2),  "u8");
  println!("ip = {}, fetching {}{}: {:?}{}",  2, 2, "u4", fetch_4_2(&m, 2),  "u8");
  println!("ip = {}, fetching {}{}: {:?}{}",  2, 3, "u4", fetch_4_3(&m, 2),  "u8");
  println!("ip = {}, fetching {}{}: {:?}{}", 42, 1, "u4", fetch_4_1(&m, 42), "u8");
  println!("ip = {}, fetching {}{}: {:?}{}", 42, 2, "u4", fetch_4_2(&m, 42), "u8");
  println!("ip = {}, fetching {}{}: {:?}{}", 42, 3, "u4", fetch_4_3(&m, 42), "u8");
  println!("ip = {}, fetching {}{}: {:?}{}",  0, 1, "u9", fetch_9_1(&m, 0),  "u8");
  println!("ip = {}, fetching {}{}: {:?}{}",  0, 2, "u9", fetch_9_2(&m, 0),  "u8");
  println!("ip = {}, fetching {}{}: {:?}{}",  0, 3, "u9", fetch_9_3(&m, 0),  "u8");
  println!("ip = {}, fetching {}{}: {:?}{}",  1, 1, "u9", fetch_9_1(&m, 1),  "u8");
  println!("ip = {}, fetching {}{}: {:?}{}",  1, 2, "u9", fetch_9_2(&m, 1),  "u8");
  println!("ip = {}, fetching {}{}: {:?}{}",  1, 3, "u9", fetch_9_3(&m, 1),  "u8");
  println!("ip = {}, fetching {}{}: {:?}{}",  2, 1, "u9", fetch_9_1(&m, 2),  "u8");
  println!("ip = {}, fetching {}{}: {:?}{}",  2, 2, "u9", fetch_9_2(&m, 2),  "u8");
  println!("ip = {}, fetching {}{}: {:?}{}",  2, 3, "u9", fetch_9_3(&m, 2),  "u8");
  println!("ip = {}, fetching {}{}: {:?}{}", 42, 1, "u9", fetch_9_1(&m, 42), "u8");
  println!("ip = {}, fetching {}{}: {:?}{}", 42, 2, "u9", fetch_9_2(&m, 42), "u8");
  println!("ip = {}, fetching {}{}: {:?}{}", 42, 3, "u9", fetch_9_3(&m, 42), "u8");
}


/*
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

*/
