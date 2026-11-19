import Lean.Data.Json

namespace GloasSsz

open Lean

/-- Native SHA-256 compresses precisely two 32-byte roots. Tree construction,
padding, collection limits, offsets, and length/field mix-ins are all in Lean. -/
@[extern "gloas_ssz_sha_pair"]
opaque shaPair (left right : @& ByteArray) : ByteArray

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

private def merkleize (leaves : Array ByteArray) (limit : Nat) : ByteArray := Id.run do
  let mut layer := leaves
  let mut padding := zero
  let mut capacity := 1
  while capacity < limit do
    let mut next := Array.emptyWithCapacity (ceilDiv layer.size 2)
    for i in [:ceilDiv layer.size 2] do
      next := next.push (shaPair layer[2*i]! (layer[2*i+1]?.getD padding))
    padding := shaPair padding padding
    layer := next
    capacity := capacity*2
  return layer[0]?.getD padding

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

end GloasSsz
