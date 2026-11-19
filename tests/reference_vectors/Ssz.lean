import Lean.Data.Json

namespace GloasSsz

open Lean

/-! FIPS 180-4 SHA-256 specialized to pairs of 32-byte SSZ roots. -/
@[inline] private def rotr32 (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

private def sha256K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

private def schedule (block : ByteArray) : Array UInt32 := Id.run do
  let mut w := Array.replicate 64 (0 : UInt32)
  for i in [0:16] do
    let b0 := block[4 * i]!.toUInt32
    let b1 := block[4 * i + 1]!.toUInt32
    let b2 := block[4 * i + 2]!.toUInt32
    let b3 := block[4 * i + 3]!.toUInt32
    w := w.set! i ((b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3)
  for i in [16:64] do
    let w15 := w[i - 15]!
    let w2  := w[i - 2]!
    let s0 := rotr32 w15 7 ^^^ rotr32 w15 18 ^^^ (w15 >>> 3)
    let s1 := rotr32 w2 17 ^^^ rotr32 w2 19 ^^^ (w2 >>> 10)
    w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)
  return w

private def compress (h w : Array UInt32) : Array UInt32 := Id.run do
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut hh := h[7]!
  for i in [0:64] do
    let s1 := rotr32 e 6 ^^^ rotr32 e 11 ^^^ rotr32 e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let temp1 := hh + s1 + ch + sha256K[i]! + w[i]!
    let s0 := rotr32 a 2 ^^^ rotr32 a 13 ^^^ rotr32 a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let temp2 := s0 + maj
    hh := g
    g := f
    f := e
    e := d + temp1
    d := c
    c := b
    b := a
    a := temp1 + temp2
  #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d,
    h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

private def iv : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

-- Every SSZ node has exactly 512 message bits. The second SHA block is constant.
private def paddingSchedule := schedule <|
  ⟨(Array.replicate 64 (0 : UInt8)).set! 0 0x80 |>.set! 62 2⟩

private def shaPair (left right : ByteArray) : ByteArray := Id.run do
  let digest := compress (compress iv (schedule (left ++ right))) paddingSchedule
  let mut out := ByteArray.emptyWithCapacity 32
  for word in digest do
    for shift in [24,16,8,0] do out := out.push ((word >>> shift).toUInt8)
  return out

inductive Size where
  | fixed (length : Nat)
  | bounded (limit : Nat)
  | progressive
  deriving Inhabited

inductive Ty where
  | bool
  | uint (width : Nat)
  | bytes (size : Size)
  | bits (size : Size)
  | seq (size : Size) (element : Ty)
  | record (fields : Array Ty) (active : Option (Array Nat))
  deriving Inhabited

private def parseSize (j : Json) : Except String Size := do
  match ← j.getObjValAs? String "mode" with
  | "fixed" => return .fixed (← j.getObjValAs? Nat "n")
  | "bounded" => return .bounded (← j.getObjValAs? Nat "n")
  | "progressive" => return .progressive
  | _ => throw "invalid SSZ collection mode"

partial def parseType (j : Json) : Except String Ty := do
  match ← j.getObjValAs? String "kind" with
  | "bool" => return .bool
  | "uint" => return .uint (← j.getObjValAs? Nat "n")
  | "bytes" => return .bytes (← parseSize j)
  | "bits" => return .bits (← parseSize j)
  | "seq" => return .seq (← parseSize j) (← parseType (← j.getObjVal? "element"))
  | "record" =>
    let fields ← (← j.getObjValAs? (Array Json) "fields").mapM parseType
    return .record fields (← j.getObjValAs? (Option (Array Nat)) "active")
  | _ => throw "unknown pinned SSZ type"

private def ceilDiv (n d : Nat) := (n + d - 1) / d

partial def fixedWidth : Ty → Option Nat
  | .bool => some 1
  | .uint n | .bytes (.fixed n) => some n
  | .bits (.fixed n) => some (ceilDiv n 8)
  | .seq (.fixed n) t => (fixedWidth t).map (· * n)
  | .record ts _ => ts.foldlM (fun acc t => (fixedWidth t).map (· + acc)) 0
  | _ => none

private def little (value width : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity width
  for i in [:width] do out := out.push ((value >>> (8*i)).toUInt8)
  return out

private def number (b : ByteArray) : Nat := Id.run do
  let mut n := 0
  for i in [:b.size] do n := n ||| (b[i]!.toNat <<< (8*i))
  return n

private def zero := little 0 32
private def chunks (b : ByteArray) : Array ByteArray := Id.run do
  let mut out := #[]
  for i in [:ceilDiv b.size 32] do
    let part := b.extract (i*32) ((i+1)*32)
    out := out.push (if part.size == 32 then part else part ++ little 0 (32-part.size))
  return out

private def zeroRoots : Array ByteArray := Id.run do
  let mut roots := #[zero]
  for _ in [:64] do roots := roots.push (shaPair roots.back! roots.back!)
  return roots

private def merkleize (leaves : Array ByteArray) (limit : Nat) : ByteArray := Id.run do
  let mut layer := leaves
  let mut height := 0
  let mut capacity := 1
  while capacity < limit do
    let mut next := Array.emptyWithCapacity (ceilDiv layer.size 2)
    for i in [:ceilDiv layer.size 2] do
      next := next.push (shaPair layer[2*i]! (layer[2*i+1]?.getD zeroRoots[height]!))
    height := height+1
    layer := next
    capacity := capacity*2
  return layer[0]?.getD zeroRoots[height]!

private partial def progressiveRoot (leaves : Array ByteArray) (start width : Nat) : ByteArray :=
  if start ≥ leaves.size then zero else
    shaPair (merkleize (leaves.extract start (start+width)) width)
      (progressiveRoot leaves (start+width) (width*4))

private def validCount (mode : Size) (n : Nat) : Bool :=
  match mode with
  | .fixed m => n == m
  | .bounded m => n ≤ m
  | .progressive => true

private def sequenceRoot (leaves : Array ByteArray) (mode : Size) (n : Nat)
    (capacity : Nat → Nat) : ByteArray :=
  match mode with
  | .fixed m => merkleize leaves (capacity m)
  | .bounded m => shaPair (merkleize leaves (capacity m)) (little n 32)
  | .progressive => shaPair (progressiveRoot leaves 0 1) (little n 32)

structure Encoded where
  wire : ByteArray
  root : ByteArray
  deriving Inhabited

/-- Split a container or homogeneous composite sequence into field byte spans.
Offsets are relative to the object and must begin exactly at the head boundary. -/
private def spans (types : Array Ty) (b : ByteArray) : Except String (Array (Nat × Nat)) := do
  let widths := types.map fixedWidth
  let head := widths.foldl (fun n w => n + w.getD 4) 0
  if head > b.size then throw "truncated SSZ head"
  let mut ranges := #[]
  let mut pending : Option (Nat × Nat) := none
  let mut cursor := 0
  for i in [:widths.size] do
    match widths[i]! with
    | some w =>
      ranges := ranges.push (cursor, cursor+w)
      cursor := cursor+w
    | none =>
      let offset := number (b.extract cursor (cursor+4))
      if offset > b.size then throw "offset past end"
      if let some (idx, previous) := pending then
        if offset < previous then throw "descending offset"
        ranges := ranges.set! idx (previous, offset)
      else if offset != head then throw "first offset differs from head length"
      ranges := ranges.push (offset, b.size)
      pending := some (i,offset)
      cursor := cursor+4
  if pending.isNone && head != b.size then throw "trailing bytes"
  return ranges

private def packFields (types : Array Ty) (values : Array Encoded) : ByteArray := Id.run do
  let headSize := types.foldl (fun n t => n + (fixedWidth t).getD 4) 0
  let mut head := ByteArray.emptyWithCapacity headSize
  let mut tail := ByteArray.empty
  for i in [:types.size] do
    let value := values[i]!.wire
    if (fixedWidth types[i]!).isSome then head := head ++ value
    else
      head := head ++ little (headSize + tail.size) 4
      tail := tail ++ value
  return head ++ tail

private def bitValue (mode : Size) (b : ByteArray) : Except String Encoded := do
  let (n, packed, wire) ← match mode with
    | .fixed n => do
      if b.size != ceilDiv n 8 then throw "bitvector length"
      if n%8 != 0 && b[b.size-1]!.toNat ≥ 2^(n%8) then throw "bitvector padding"
      pure (n, b, b)
    | _ => do
      if b.size == 0 then throw "bitlist lacks terminator"
      let last := b[b.size-1]!.toNat
      if last == 0 then throw "bitlist lacks terminator"
      let bit := last.log2
      let n := (b.size-1)*8 + bit
      if !validCount mode n then throw "bitlist exceeds capacity"
      let body := b.extract 0 (b.size-1)
      let value := last - (1 <<< bit)
      let packed := if bit == 0 then body else body.push value.toUInt8
      pure (n, packed, body.push (value ||| (1 <<< bit)).toUInt8)
  return ⟨wire, sequenceRoot (chunks packed) mode n (fun k => ceilDiv k 256)⟩

/-- Decode child boundaries and re-encode canonical offsets while computing
the typed tree root. Scalar sequences retain their packed fixed-width wire layout. -/
partial def codec (t : Ty) (b : ByteArray) : Except String Encoded := do
  match t with
  | .bool =>
    if b.size != 1 || b[0]! > 1 then throw "invalid boolean"
    return ⟨little (number b) 1, little (number b) 32⟩
  | .uint n =>
    if b.size != n || n > 32 then throw "integer width"
    return ⟨little (number b) n, little (number b) 32⟩
  | .bytes mode =>
    if !validCount mode b.size then throw "byte length"
    return ⟨b, sequenceRoot (chunks b) mode b.size (fun k => ceilDiv k 32)⟩
  | .bits mode => bitValue mode b
  | .record fields active =>
    let ranges ← spans fields b
    let mut values := #[]
    for i in [:fields.size] do
      let (s,e) := ranges[i]!
      values := values.push (← codec fields[i]! (b.extract s e))
    let roots := values.map Encoded.root
    let root ← match active with
      | none => pure (merkleize roots roots.size)
      | some positions => do
        let mut leaves := #[]
        let mut mask := 0
        let mut field := 0
        for i in [:positions.size] do
          if positions[i]! == 0 then leaves := leaves.push zero
          else
            let some root := roots[field]? | throw "progressive field map overflow"
            leaves := leaves.push root
            mask := mask ||| (1 <<< i)
            field := field+1
        if field != roots.size then throw "progressive field map incomplete"
        pure (shaPair (progressiveRoot leaves 0 1) (little mask 32))
    return ⟨packFields fields values, root⟩
  | .seq mode element =>
    let size ← match fixedWidth element with
      | some width => do
        if width == 0 || b.size % width != 0 then throw "misaligned sequence"
        pure (b.size/width)
      | none => do
        if b.size == 0 then pure 0 else
          if b.size < 4 then throw "missing sequence offsets"
          let first := number (b.extract 0 4)
          if first == 0 || first > b.size || first % 4 != 0 then throw "invalid first offset"
          pure (first/4)
    if !validCount mode size then throw "sequence count"
    let basic := match element with | .bool => some 1 | .uint n => some n | _ => none
    if let some width := basic then
      if let .bool := element then
        for byte in b.data do if byte > 1 then throw "invalid packed boolean"
      return ⟨b, sequenceRoot (chunks b) mode size (fun k => ceilDiv (k*width) 32)⟩
    let types := Array.replicate size element
    let ranges ← spans types b
    let mut values := #[]
    for (s,e) in ranges do values := values.push (← codec element (b.extract s e))
    return ⟨packFields types values, sequenceRoot (values.map Encoded.root) mode size id⟩

@[export gloas_run_ssz]
def check (schema : String) (input : ByteArray) : String := Id.run do
  let answer : Except String String := do
    let t ← parseType (← Lean.Json.parse schema)
    let result ← codec t input
    if result.wire != input then throw "SSZ re-encoding differs from input"
    return String.ofList (result.root.toList.flatMap (fun (byte : UInt8) =>
      let digits := "0123456789abcdef".toList
      [digits[byte.toNat/16]!, digits[byte.toNat%16]!]))
  match answer with
  | .ok root => return root
  | .error err => return "error: " ++ err

private def signingRoot (objectRoot : ByteArray) (domainType : Nat)
    (version genesisRoot : ByteArray) : ByteArray :=
  let forkDataRoot := shaPair (version ++ little 0 28) genesisRoot
  shaPair objectRoot (little domainType 4 ++ forkDataRoot.extract 0 28)

/-- Sign the pinned four-field PTC attestation data with DOMAIN_PTC_ATTESTER. -/
@[export gloas_ptc_signing_root]
def ptcSigningRoot (message version genesisRoot : ByteArray) : ByteArray := Id.run do
  if version.size != 4 || genesisRoot.size != 32 then return ByteArray.empty
  let typ := Ty.record #[.bytes (.fixed 32), .uint 8, .bool, .bool] none
  let .ok parsed := codec typ message | return ByteArray.empty
  return signingRoot parsed.root 12 version genesisRoot

/-- Gloas builder deposits sign DepositMessage using DOMAIN_BUILDER_DEPOSIT
and the preset genesis fork version, with a zero genesis validators root.
The ABI accepts the 88-byte fixed-width message and four version bytes. -/
@[export gloas_builder_signing_root]
def builderSigningRoot (message forkVersion : ByteArray) : ByteArray := Id.run do
  if message.size != 88 || forkVersion.size != 4 then return ByteArray.empty
  let messageType := Ty.record #[.bytes (.fixed 48), .bytes (.fixed 32), .uint 8] none
  let .ok parsed := codec messageType message | return ByteArray.empty
  return signingRoot parsed.root 14 forkVersion zero

end GloasSsz
