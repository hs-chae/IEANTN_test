import FFTUntrustedData
import FFTForestTrace
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace FapForest17
open RH080Next.FFT.IntegerModel
def seed : CInt := ((Int.ofNat 999999998851026827562673307794554109),(Int.negSucc 47936899603066884549003990494658))
pair_certificate w01 from "w-01.csv" count 1
pair_certificate w02 from "w-02.csv" count 2
pair_certificate w03 from "w-03.csv" count 4
pair_certificate w04 from "w-04.csv" count 8
pair_certificate w05 from "w-05.csv" count 16
pair_certificate w06 from "w-06.csv" count 32
pair_certificate w07 from "w-07.csv" count 64
pair_certificate w08 from "w-08.csv" count 128
pair_certificate w09 from "w-09.csv" count 256
pair_certificate w10 from "w-10.csv" count 512
pair_certificate w11 from "w-11.csv" count 1024
pair_certificate w12 from "w-12.csv" count 2048
pair_certificate w13 from "w-13.csv" count 4096
pair_certificate w14 from "w-14.csv" count 8192
pair_certificate w15 from "w-15.csv" count 16384
pair_certificate w16 from "w-16.csv" count 32768
pair_certificate w17 from "w-17.csv" count 65536
def stages : Nat → List CInt
  | 0 => []
  | 1 => w01
  | 2 => w02
  | 3 => w03
  | 4 => w04
  | 5 => w05
  | 6 => w06
  | 7 => w07
  | 8 => w08
  | 9 => w09
  | 10 => w10
  | 11 => w11
  | 12 => w12
  | 13 => w13
  | 14 => w14
  | 15 => w15
  | 16 => w16
  | 17 => w17
  | _ => []
def leaves : List (List CInt) := (List.range 131072).map (fun j => [input 131072 j])
end FapForest17
