#[macro_use]
extern crate do_with_in;

use do_with_in::*;
use std::cmp;

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
                    // ip is based on MEM_SIMULATING_TYPE_SIZE, and goes out to MEM_SIMULATING_CHUNKS, wrapping around at (MEM_STORE_TYPE_SIZE * MEM_STORE_CHUNKS)
                  {
                    let very_first_bit = (safe_ip * $MEM_SIMULATING_TYPE_SIZE);
                    let total_bits = $MEM_SIMULATING_TYPE_SIZE * $MEM_SIMULATING_CHUNKS;
                    let bits_already_eaten = ($1 * $MEM_RETURN_TYPE_SIZE);
                    let first_bit = (very_first_bit + bits_already_eaten);
                    let bits_left_this_mouthful = cmp::min(total_bits - bits_already_eaten, $MEM_RETURN_TYPE_SIZE);
                    let base: usize = first_bit / $MEM_STORE_TYPE_SIZE as usize;
                    let num: usize = (((first_bit + bits_left_this_mouthful - 1) / $MEM_STORE_TYPE_SIZE) as usize) - base;
                    let start_offset = first_bit % $MEM_STORE_TYPE_SIZE;
                    //println!("For ip: {} and $1: {} and base: {} and num: {}", ip, $1, base, num);
                    let mut out: $MEM_RETURN_TYPE = 0;
                    out |= ((self.mem[base] >> start_offset) & ((1 << bits_left_this_mouthful) - 1)) as $MEM_RETURN_TYPE;
                    let mut i = 1;
                    while i <= num {
                      let mask = (((1 << (bits_left_this_mouthful - ((i - 1) * $MEM_STORE_TYPE_SIZE))) - 1) as $MEM_RETURN_TYPE);
                      //println!("For start_bits: {}, end bits: {}, bits: {:#b}", start_bits, end_bits, mask);
                      out |= (self.mem[base + i] << ($MEM_STORE_TYPE_SIZE - (start_offset + ((i - 1) * $MEM_RETURN_TYPE_SIZE)))) as $MEM_RETURN_TYPE & mask;
                      i+=1;
                    }
                    out
                  },
            )
          $(mk bit2 // $1 is current output chunk number, $2 is the final output chunk number
                    // ip is based on MEM_SIMULATING_TYPE_SIZE, and goes out to MEM_SIMULATING_CHUNKS, wrapping around at (MEM_STORE_TYPE_SIZE * MEM_STORE_CHUNKS) bits
                    // Each cell has to check for overflow
                  {
                    let very_first_bit = (safe_ip * $MEM_SIMULATING_TYPE_SIZE);
                    let total_bits = $MEM_SIMULATING_TYPE_SIZE * $MEM_SIMULATING_CHUNKS;
                    let bits_already_eaten = ($1 * $MEM_RETURN_TYPE_SIZE);
                    let first_bit = (very_first_bit + bits_already_eaten);
                    let bits_left_this_mouthful = cmp::min(total_bits - bits_already_eaten, $MEM_RETURN_TYPE_SIZE);
                    let base: usize = first_bit / $MEM_STORE_TYPE_SIZE as usize;
                    let num: usize = (((first_bit + bits_left_this_mouthful - 1) / $MEM_STORE_TYPE_SIZE) as usize) - base;
                    let start_offset = first_bit % $MEM_STORE_TYPE_SIZE;
                    //println!("For ip: {} and $1: {} and base: {} and num: {}", ip, $1, base, num);
                    let mut out: $MEM_RETURN_TYPE = 0;
                    out |= ((self.mem[base % $MEM_STORE_CHUNKS] >> start_offset) & ((1 << bits_left_this_mouthful) - 1)) as $MEM_RETURN_TYPE;
                    let mut i = 1;
                    while i <= num {
                      let mask = (((1 << (bits_left_this_mouthful - ((i - 1) * $MEM_STORE_TYPE_SIZE))) - 1) as $MEM_RETURN_TYPE);
                      //println!("For start_bits: {}, end bits: {}, bits: {:#b}", start_bits, end_bits, mask);
                      out |= (self.mem[(base + i) % $MEM_STORE_CHUNKS] << ($MEM_STORE_TYPE_SIZE - (start_offset + ((i - 1) * $MEM_RETURN_TYPE_SIZE)))) as $MEM_RETURN_TYPE & mask;
                      i+=1;
                    }
                    out
                  },
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

  $(mkFetch u32 32 512 u16 16 1 3  1 fetch_u32_into_u16_3_1)
  $(mkFetch u32 32 512 u64 64 1 3  1 fetch_u32_into_u64_3_1)
  $(mkFetch u32 32 512 u16 16 2 30 1 fetch_u32_into_u16_30_1)
  $(mkFetch u32 32 512 u64 64 1 30 1 fetch_u32_into_u64_30_1)

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

#[test]
fn testFetch1() {
  let mut m: Mem<usize, 256> = Mem { mem: [0usize; 256], };
  m.mem[0] = 0b1111_0010_1111_0000_1000_0100_0010_0001;
  assert_eq!(fetch_4_1(&m, 0), [0b0001]);
  assert_eq!(fetch_4_2(&m, 0), [0b0010_0001]);
  assert_eq!(fetch_4_3(&m, 0), [0b0010_0001, 0b0100]);
  assert_eq!(fetch_9_1(&m, 0), [0b0010_0001, 0b0]);
  assert_eq!(fetch_9_2(&m, 0), [0b0010_0001, 0b1000_0100, 0b00]);
  assert_eq!(fetch_9_3(&m, 0), [0b0010_0001, 0b1000_0100, 0b1111_0000, 0b010]);
  assert_eq!(fetch_9_1(&m, 1), [0b01000_010, 0b0]);
}

#[test]
fn testFetch2() {
  let mut m: Mem<u32, 512> = Mem { mem: [0u32; 512], };
  m.mem[0] = 0b1111_0010_1111_0000_1000_0100_0010_0001;
  m.mem[1] = 0b0000_1000_1100_0111_1011_1101_1110_1111;
  assert_eq!(fetch_u32_into_u16_3_1(&m, 0), [0b001]);
  assert_eq!(fetch_u32_into_u64_3_1(&m, 0), [0b001]);
  assert_eq!(fetch_u32_into_u16_30_1(&m, 0), [0b1000_0100_0010_0001, 0b11_0010_1111_0000]);
  assert_eq!(fetch_u32_into_u64_30_1(&m, 0), [0b11_0010_1111_0000_1000_0100_0010_0001]);
  assert_eq!(fetch_u32_into_u16_3_1(&m, 1), [0b100]);
  assert_eq!(fetch_u32_into_u64_3_1(&m, 1), [0b100]);
  assert_eq!(fetch_u32_into_u16_30_1(&m, 1), [0b11_1101_1110_1111_11, 0b1000_1100_0111_10]);
  assert_eq!(fetch_u32_into_u64_30_1(&m, 1), [0b1000_1100_0111_1011_1101_1110_1111_11]);
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
