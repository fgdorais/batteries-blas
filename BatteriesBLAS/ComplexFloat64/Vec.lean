/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ScalarArray
public import BatteriesBLAS.ComplexFloat64.Basic

/-!
# Complex vectors

`Vec n` is a vector of `n` complex numbers, stored in a `Float64Array` as in Fortran: each element
takes two consecutive entries of the array, its real part and then its imaginary part. As in the
reference BLAS, the offset and the stride count elements, not entries: element `i` has its real
part at the index `2 * off + 2 * inc * i` and its imaginary part at the next index. The other
entries of the array are not part of the vector, and the routines that update a vector leave them
unchanged.

The real parts are at the steps of the scalar-arrays `Stride` `x.reStride`, and the imaginary
parts at those of `x.imStride`, so that the loops and lemmas of scalar-arrays on strides apply to
each, and `modifyAt2` updates both parts of each element together.
-/

open ScalarArray

namespace BLAS.ComplexFloat64

/--
A vector of `n` complex numbers, stored in a `Float64Array` from the element `off`, with the
stride `inc`, both counted in elements of two entries each. The stride is positive, unless the
vector has at most one element, so that its elements are at distinct indices.
-/
public structure Vec (n : Nat) where
  /-- The array that holds the parts of the elements. -/
  data : Float64Array
  /-- The position of the first element, in elements. -/
  off : Nat
  /-- The distance between two consecutive elements, in elements. -/
  inc : Nat
  /-- The stride is positive, unless the vector has at most one element. -/
  inc_pos : 0 < inc ∨ n ≤ 1
  /-- The imaginary part of the last element is in the array. -/
  bound : n = 0 ∨ 2 * off + 2 * inc * (n - 1) + 1 < data.size

namespace Vec

variable {n : Nat}

/-- The indices `2 * off + 2 * inc * i` of the real parts, as a scalar-arrays `Stride`. -/
@[expose] public def reStride (x : Vec n) : Stride := ⟨2 * x.off, 2 * x.inc⟩

/-- The indices `2 * off + 1 + 2 * inc * i` of the imaginary parts, as a scalar-arrays `Stride`. -/
@[expose] public def imStride (x : Vec n) : Stride := ⟨2 * x.off + 1, 2 * x.inc⟩

public theorem idx_reStride (x : Vec n) (i : Nat) :
    x.reStride.idx i = 2 * x.off + 2 * x.inc * i := rfl

public theorem idx_imStride (x : Vec n) (i : Nat) :
    x.imStride.idx i = 2 * x.off + 1 + 2 * x.inc * i := rfl

/-- The real parts fit in the array, at distinct indices. -/
public theorem fits_re (x : Vec n) : x.reStride.Fits n x.data.size :=
  by
  constructor
  · rcases x.inc_pos with h | h
    · exact .inl (by simp [reStride]; lia)
    · exact .inr h
  · rcases x.bound with h | h
    · exact .inl h
    · exact .inr (by simp [reStride, Stride.idx]; lia)

/-- The imaginary parts fit in the array, at distinct indices. -/
public theorem fits_im (x : Vec n) : x.imStride.Fits n x.data.size :=
  by
  constructor
  · rcases x.inc_pos with h | h
    · exact .inl (by simp [imStride]; lia)
    · exact .inr h
  · rcases x.bound with h | h
    · exact .inl h
    · exact .inr (by simp [imStride, Stride.idx]; lia)

/-- No real part is at the index of an imaginary part. -/
public theorem re_ne_im (x : Vec n) (i j : Nat) : x.reStride.idx i ≠ x.imStride.idx j := by
  simp only [idx_reStride, idx_imStride]; lia

/-- The index of the real part of element `i < n` is in the array. -/
public theorem re_lt (x : Vec n) {i : Nat} (h : i < n) :
    2 * x.off + 2 * x.inc * i < x.data.size :=
  x.fits_re.idx_lt h

/-- The index of the imaginary part of element `i < n` is in the array. -/
public theorem im_lt (x : Vec n) {i : Nat} (h : i < n) :
    2 * x.off + 1 + 2 * x.inc * i < x.data.size :=
  x.fits_im.idx_lt h

/-- A vector has at most half as many elements as its array has entries. -/
public theorem two_mul_le_size (x : Vec n) : 2 * n ≤ x.data.size := by
  rcases Nat.eq_zero_or_pos n with h | h
  · lia
  · have := x.im_lt (i := n - 1) (by lia)
    rcases x.inc_pos with h' | h'
    · have : n - 1 ≤ x.inc * (n - 1) := Nat.le_mul_of_pos_left _ h'
      lia
    · lia

public instance : GetElem (Vec n) Nat ComplexFloat fun _ i => i < n where
  getElem x i h := ⟨x.data[2 * x.off + 2 * x.inc * i]'(x.re_lt h),
    x.data[2 * x.off + 1 + 2 * x.inc * i]'(x.im_lt h)⟩

public theorem getElem_def (x : Vec n) (i : Nat) (h : i < n) :
    x[i] = ⟨x.data[2 * x.off + 2 * x.inc * i]'(x.re_lt h),
      x.data[2 * x.off + 1 + 2 * x.inc * i]'(x.im_lt h)⟩ := rfl

@[simp] public theorem re_getElem (x : Vec n) (i : Nat) (h : i < n) :
    x[i].re = x.data[2 * x.off + 2 * x.inc * i]'(x.re_lt h) := rfl

@[simp] public theorem im_getElem (x : Vec n) (i : Nat) (h : i < n) :
    x[i].im = x.data[2 * x.off + 1 + 2 * x.inc * i]'(x.im_lt h) := rfl

/--
The `USize` index of the real part of element `i < n` doesn't wrap around, in an array of `USize`
size.
-/
public theorem toNat_re (x : Vec n) (hs : x.data.size < USize.size) {i : USize}
    (h : i.toNat < n) :
    ((2 * x.off).toUSize + (2 * x.inc).toUSize * i).toNat = 2 * x.off + 2 * x.inc * i.toNat :=
  Stride.toNat_idx_toUSize x.fits_re hs h

/--
The `USize` index of the imaginary part of element `i < n` doesn't wrap around, in an array of
`USize` size.
-/
public theorem toNat_im (x : Vec n) (hs : x.data.size < USize.size) {i : USize}
    (h : i.toNat < n) :
    ((2 * x.off + 1).toUSize + (2 * x.inc).toUSize * i).toNat =
      2 * x.off + 1 + 2 * x.inc * i.toNat :=
  Stride.toNat_idx_toUSize x.fits_im hs h

public theorem toNat_re_lt (x : Vec n) (hs : x.data.size < USize.size) {i : USize}
    (h : i.toNat < n) : ((2 * x.off).toUSize + (2 * x.inc).toUSize * i).toNat < x.data.size :=
  Stride.toNat_idx_toUSize_lt x.fits_re hs h

public theorem toNat_im_lt (x : Vec n) (hs : x.data.size < USize.size) {i : USize}
    (h : i.toNat < n) :
    ((2 * x.off + 1).toUSize + (2 * x.inc).toUSize * i).toNat < x.data.size :=
  Stride.toNat_idx_toUSize_lt x.fits_im hs h

/--
The element at the `USize` index `i`, in a vector whose array has a `USize` size, given the
`USize` indices `o` and `o1` of the real and imaginary parts of element `0` and the stride `c`
between entries. It compiles to two inline loads. A loop computes `o`, `o1` and `c` once, before it
starts, rather than at each step. It is irreducible, so that elaborating a loop doesn't unfold it
into the loads of `Float64Array`.
-/
@[inline, irreducible] public def uget (x : Vec n) (o o1 c : USize) (ho : (2 * x.off).toUSize = o)
    (ho1 : (2 * x.off + 1).toUSize = o1) (hc : (2 * x.inc).toUSize = c)
    (hs : x.data.size < USize.size) (i : USize) (h : i.toNat < n) : ComplexFloat :=
  ⟨x.data.uget (o + c * i) (by rw [← ho, ← hc]; exact x.toNat_re_lt hs h),
    x.data.uget (o1 + c * i) (by rw [← ho1, ← hc]; exact x.toNat_im_lt hs h)⟩

@[simp] public theorem uget_eq_getElem (x : Vec n) (o o1 c : USize)
    (ho : (2 * x.off).toUSize = o) (ho1 : (2 * x.off + 1).toUSize = o1)
    (hc : (2 * x.inc).toUSize = c) (hs : x.data.size < USize.size) (i : USize)
    (h : i.toNat < n) : x.uget o o1 c ho ho1 hc hs i h = x[i.toNat] := by
  subst ho ho1 hc
  simp only [uget, Float64Array.uget_eq_getElem, getElem_def, x.toNat_re hs h, x.toNat_im hs h]

/--
The contiguous vector of the elements of `a`: element `i` is `(a[2 * i], a[2 * i + 1])`.
-/
@[expose] public def ofArray (a : Float64Array) (h : a.size = 2 * n) : Vec n where
  data := a
  off := 0
  inc := 1
  inc_pos := Or.inl (by decide)
  bound := by
    rcases Nat.eq_zero_or_pos n with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by lia)

@[simp] public theorem data_ofArray (a : Float64Array) (h : a.size = 2 * n) :
    (ofArray a h).data = a :=
  rfl

@[simp] public theorem getElem_ofArray (a : Float64Array) (h : a.size = 2 * n) (i : Nat)
    (hi : i < n) : (ofArray a h)[i] = ⟨a[2 * i]'(by lia), a[2 * i + 1]'(by lia)⟩ := by
  simp only [getElem_def, ofArray]
  congr 1 <;> simp [Nat.add_comm]

/--
The vector of `n` elements of `a` from the element `off` with the stride `inc`, both counted in
elements of two entries, if they are in `a` and the stride is positive or `n ≤ 1`.
-/
public def ofStride? (a : Float64Array) (off inc : Nat) : Option (Vec n) :=
  if h : (0 < inc ∨ n ≤ 1) ∧ (n = 0 ∨ 2 * off + 2 * inc * (n - 1) + 1 < a.size) then
    some ⟨a, off, inc, h.1, h.2⟩
  else none

/-- The contiguous vector with the elements `f i`. -/
public def ofFn (f : Fin n → ComplexFloat) : Vec n :=
  ofArray (.ofFn (n := 2 * n) fun k =>
    let z := f ⟨k.val / 2, by lia⟩
    if k.val % 2 = 0 then z.re else z.im) (by simp)

@[simp] public theorem getElem_ofFn (f : Fin n → ComplexFloat) (i : Nat) (h : i < n) :
    (ofFn f)[i] = f ⟨i, h⟩ := by
  simp only [ofFn, getElem_ofArray, Float64Array.getElem_ofFn]
  have h₁ : 2 * i / 2 = i := by lia
  have h₂ : (2 * i + 1) / 2 = i := by lia
  simp [h₁, h₂, Nat.add_mod]

@[simp] public theorem off_ofFn (f : Fin n → ComplexFloat) : (ofFn f).off = 0 := by
  simp [ofFn, ofArray]

@[simp] public theorem inc_ofFn (f : Fin n → ComplexFloat) : (ofFn f).inc = 1 := by
  simp [ofFn, ofArray]

/-- The contiguous vector with the elements of `l`, of length `n`. -/
public def ofList (l : List ComplexFloat) (h : l.length = n := by simp) : Vec n :=
  ofFn fun i => l[i.val]'(by rw [h]; exact i.isLt)

/-- The elements as a list. -/
public def toList (x : Vec n) : List ComplexFloat := List.ofFn fun i : Fin n => x[i.val]

@[simp] public theorem length_toList (x : Vec n) : x.toList.length = n := by
  simp [toList]

@[simp] public theorem getElem_toList (x : Vec n) (i : Nat) (h : i < x.toList.length) :
    x.toList[i] = x[i]'(by simpa using h) := by
  simp [toList]

end Vec

end BLAS.ComplexFloat64
