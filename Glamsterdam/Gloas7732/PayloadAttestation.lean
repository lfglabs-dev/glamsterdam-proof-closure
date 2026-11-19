namespace Glamsterdam.Gloas7732

/-- Select the signing participants for the pinned Gloas payload attestation.
The parent root and previous slot checks precede the lookup. Repeated members
occupy distinct PTC positions, so all selected occurrences enter the signature. -/
def payloadAttesters (slot attestedSlot slotsPerEpoch forkEpoch parentRoot attestedRoot : Nat)
    (window : Array (Array Nat)) (bits : Array Bool) : Option (List Nat) := do
  if slotsPerEpoch == 0 || attestedSlot+1 != slot || parentRoot != attestedRoot then none else
    let epoch := attestedSlot / slotsPerEpoch
    let currentEpoch := slot / slotsPerEpoch
    if epoch < forkEpoch then none else
      let offset := (epoch+1-currentEpoch)*slotsPerEpoch + attestedSlot%slotsPerEpoch
      let committee ← window[offset]?
      if bits.size != committee.size then none else
        let indices := (committee.zip bits).toList.filterMap (fun (v, selected) =>
          if selected then some v else none)
        if indices.isEmpty then none else some (indices.mergeSort)

end Glamsterdam.Gloas7732
