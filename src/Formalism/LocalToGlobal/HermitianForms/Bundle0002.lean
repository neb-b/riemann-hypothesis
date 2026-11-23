module

public import Formalism.LocalToGlobal.HermitianForms.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.HermitianForms.DefsChi
section
noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Forms

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {gp : Fin 2 → ℕ}

structure CharacterCompatible (G : GLoc F E σ gp) (m : ℕ) : Prop where

  dist : ∀ i v h a b, a < m → b < m → G.chiB i v h a = G.chiB i v h b → a = b

  same : ∀ i v h v' h' a (n : ℤ), a < m → G.chiB i v h a (n : kv F v) = G.chiB i v' h' a (n : kv F v')

  pow : ∀ i, ∃ om : MulChar (ZMod (gp i)) ℂ, orderOf om = gp i - 1 ∧
    ∀ v h a (n : ℤ), a < m → G.chiB i v h a (n : kv F v) = (om ^ (2 * (a + 1))) (n : ZMod (gp i))

end Formalism.L2.Forms

end
end

-- bundled from Formalism.LocalToGlobal.HermitianForms.DefsSym
section
noncomputable section

namespace Formalism.L2.Forms

section Sym

variable {κ : Type} [Field κ] {n : ℕ}

def rSym (k rS : ℕ) : ℕ := k + 2 * rS + 1

def posSym (k rS x : ℕ) : ℕ := if x < k then rS + x else if x - k < rS then x - k else x

def lvSym (k rS t x : ℕ) : ℕ := if x < rSym k rS then posSym k rS x else rSym k rS + (x - rSym k rS) / t

def InJSym (k rS t : ℕ) (zl : Bool) (M : Matrix (Fin n) (Fin n) κ) : Prop :=
  (∀ x y : Fin n, lvSym k rS t y < lvSym k rS t x → M x y = 0) ∧
  (∀ x : Fin n, (x : ℕ) < rSym k rS → M x x = 1) ∧
  (∀ x y : Fin n, (x : ℕ) < k → (y : ℕ) = k + rS → M x y = 0) ∧
  (zl = true → ∀ x y : Fin n, (y : ℕ) + 1 = n →
    M x y = (if x = y then 1 else 0) ∧ M y x = (if x = y then 1 else 0))

theorem posSym_lt {k rS x : ℕ} (hx : x < rSym k rS) : posSym k rS x < rSym k rS := by
  unfold posSym rSym at *
  split_ifs <;> omega

theorem lvSym_of_lt {k rS t x : ℕ} (hx : x < rSym k rS) : lvSym k rS t x = posSym k rS x := by
  unfold lvSym
  rw [if_pos hx]

theorem lvSym_of_ge {k rS t x : ℕ} (hx : ¬ x < rSym k rS) : rSym k rS ≤ lvSym k rS t x := by
  unfold lvSym
  rw [if_neg hx]
  exact Nat.le_add_right _ _

theorem posSym_inj {k rS x z : ℕ} (hx : x < rSym k rS) (hz : z < rSym k rS) (h : posSym k rS z = posSym k rS x) : z = x := by
  unfold posSym rSym at *
  split_ifs at h <;> omega

theorem lvSym_eq {k rS t x z : ℕ} (hx : x < rSym k rS) (h : lvSym k rS t z = lvSym k rS t x) : z = x := by
  rw [lvSym_of_lt hx] at h
  by_cases hz : z < rSym k rS
  · rw [lvSym_of_lt hz] at h
    exact posSym_inj hx hz h
  · have h1 := lvSym_of_ge (t := t) hz
    have h2 := posSym_lt hx
    omega

theorem lvSym_mid {k rS t x z : ℕ} (hx : x < k) (h1 : ¬ lvSym k rS t z < lvSym k rS t x)
    (h2 : ¬ lvSym k rS t (k + rS) < lvSym k rS t z) (h3 : ¬ z < k) : z = k + rS := by
  have hxr : x < rSym k rS := by unfold rSym; omega
  have hmr : k + rS < rSym k rS := by unfold rSym; omega
  rw [lvSym_of_lt hxr] at h1
  rw [lvSym_of_lt hmr] at h2
  by_cases hz : z < rSym k rS
  · rw [lvSym_of_lt hz] at h1 h2
    unfold posSym rSym at *
    split_ifs at h1 h2 <;> omega
  · have h4 := lvSym_of_ge (t := t) hz
    have h5 := posSym_lt hmr
    omega

theorem InJSym_mul {k rS t : ℕ} {zl : Bool} {M N : Matrix (Fin n) (Fin n) κ} (hM : InJSym k rS t zl M)
    (hN : InJSym k rS t zl N) : InJSym k rS t zl (M * N) := by
  obtain ⟨hM1, hM2, hM3, hM4⟩ := hM
  obtain ⟨hN1, hN2, hN3, hN4⟩ := hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hz : lvSym k rS t z < lvSym k rS t x
    · rw [hM1 x z hz, zero_mul]
    · rw [hN1 z y (by omega), mul_zero]
  · intro x hx
    rw [Matrix.mul_apply, Finset.sum_eq_single x]
    · rw [hM2 x hx, hN2 x hx, one_mul]
    · intro z _ hzx
      by_cases hz : lvSym k rS t z < lvSym k rS t x
      · rw [hM1 x z hz, zero_mul]
      · by_cases hz' : lvSym k rS t x < lvSym k rS t z
        · rw [hN1 z x hz', mul_zero]
        · exact absurd (Fin.ext (lvSym_eq (t := t) hx (by omega))) hzx
    · intro h
      exact absurd (Finset.mem_univ x) h
  · intro x y hx hy
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hz : lvSym k rS t z < lvSym k rS t x
    · rw [hM1 x z hz, zero_mul]
    by_cases hz' : lvSym k rS t y < lvSym k rS t z
    · rw [hN1 z y hz', mul_zero]
    by_cases hzk : (z : ℕ) < k
    · rw [hN3 z y hzk hy, mul_zero]
    have hzy : z = y := Fin.ext (by rw [hy]; exact lvSym_mid hx hz (by rwa [← hy]) hzk)
    subst hzy
    rw [hM3 x z hx hy, zero_mul]
  · intro hzl x y hy
    have h4M := hM4 hzl
    have h4N := hN4 hzl
    constructor
    · rw [Matrix.mul_apply, Finset.sum_eq_single y]
      · rw [(h4N y y hy).1, if_pos rfl, mul_one, (h4M x y hy).1]
      · intro z _ hzy
        rw [(h4N z y hy).1, if_neg hzy, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ y) h
    · rw [Matrix.mul_apply, Finset.sum_eq_single y]
      · rw [(h4M y y hy).2, if_pos rfl, one_mul, (h4N x y hy).2]
      · intro z _ hzy
        rw [(h4M z y hy).2, if_neg hzy, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ y) h

theorem InJSym_one (k rS t : ℕ) (zl : Bool) : InJSym k rS t zl (1 : Matrix (Fin n) (Fin n) κ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y h
    have hxy : x ≠ y := by
      rintro rfl
      exact lt_irrefl _ h
    exact Matrix.one_apply_ne hxy
  · intro x _
    exact Matrix.one_apply_eq x
  · intro x y hx hy
    refine Matrix.one_apply_ne ?_
    intro h
    rw [h] at hx
    omega
  · intro _ x y _
    refine ⟨Matrix.one_apply, ?_⟩
    rw [Matrix.one_apply]
    rcases eq_or_ne x y with h | h
    · subst h
      simp
    · rw [if_neg (Ne.symm h), if_neg h]

variable (κ n)

def JSymG (k rS t : ℕ) (zl : Bool) : Subgroup (GL (Fin n) κ) where
  carrier := {M | InJSym k rS t zl (M : Matrix (Fin n) (Fin n) κ) ∧
    InJSym k rS t zl ((M⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ)}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact InJSym_mul ha hb
    · rw [mul_inv_rev, Units.val_mul]; exact InJSym_mul hb' ha'
  one_mem' := ⟨by simpa using InJSym_one k rS t zl, by simpa using InJSym_one k rS t zl⟩
  inv_mem' := by
    rintro a ⟨h, h'⟩; exact ⟨h', by simpa using h⟩

variable {κ n}

def lamSym (ψ : AddChar κ ℂ) (χ : ℕ → MulChar κ ℂ) (k rS t nb : ℕ) (M : Matrix (Fin n) (Fin n) κ) : ℂ :=
  lamJ ψ χ (rSym k rS) t nb k M

end Sym

section Ext

def insB (k c x : ℕ) : ℕ := if x < k then x else x + c

def eBf (N k c : ℕ) (hk : k ≤ N) : Fin N ⊕ Fin c → Fin (N + c) :=
  Sum.elim (fun x => ⟨insB k c x, by have := x.isLt; unfold insB; split_ifs <;> omega⟩)
    (fun i => ⟨k + i, by have := i.isLt; omega⟩)

theorem eBf_inj (N k c : ℕ) (hk : k ≤ N) : Function.Injective (eBf N k c hk) := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [eBf, Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq, insB, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, Fin.ext_iff] at h ⊢ <;>
    have ha := a.isLt <;> have hb := b.isLt <;> (try split_ifs at h) <;> omega

def eB (N k c : ℕ) (hk : k ≤ N) : Fin N ⊕ Fin c ≃ Fin (N + c) :=
  Equiv.ofBijective (eBf N k c hk) ((Fintype.bijective_iff_injective_and_card _).2 ⟨eBf_inj N k c hk, by simp⟩)

variable (κ : Type) [Field κ]

def extMon (N k c : ℕ) (hk : k ≤ N) : Matrix (Fin N) (Fin N) κ →* Matrix (Fin (N + c)) (Fin (N + c)) κ where
  toFun M := Matrix.reindex (eB N k c hk) (eB N k c hk) (Matrix.fromBlocks M 0 0 1)
  map_one' := by simp [Matrix.fromBlocks_one]
  map_mul' M M' := by
    rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
      Matrix.fromBlocks_multiply]
    simp

def HX (N k rS t c : ℕ) (hk : k ≤ N) : Subgroup (GL (Fin N) κ) :=
  (JSymG κ (N + c) k rS t false).comap (Units.map (extMon κ N k c hk))

variable {κ}

def lamX (ψ : AddChar κ ℂ) (χ : ℕ → MulChar κ ℂ) (N k rS t c nb : ℕ) (hk : k ≤ N) (M : Matrix (Fin N) (Fin N) κ) : ℂ :=
  lamSym ψ χ k rS t nb (extMon κ N k c hk M)

end Ext

end Formalism.L2.Forms
end
end

-- bundled from Formalism.LocalToGlobal.HermitianForms.TiedStep
section
noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable (D : D7)

def sigD : D.host.E →ₐ[D.host.F] D.host.E := letI := D.host.cmStar; D.sp.cm.sig

def embT : D.what₂.Tau → D.host.E →+* ℂ := fun τ => D.host.emb (D.eTau τ : D.R.GG)

theorem rankN (i : ℕ) (hi : i ≤ D.R.m) : letI := D.host.cmStar; (D.sp.X i).rank = D.R.N i :=
  letI := D.host.cmStar; D.sp.X_rank i hi

def gramN (i : ℕ) (hi : i ≤ D.R.m) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E :=
  letI := D.host.cmStar
  (D.sp.X i).gram.reindex (finCongr (rankN D i hi)) (finCongr (rankN D i hi))

def clsCrd (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  letI := D.host.cmStar
  (D.clsLat u i c).map ((((D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm) :
      (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) :
      (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))

def selfDualLatticeCoords (i : ℕ) (hi : i ≤ D.R.m) : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  letI := D.host.cmStar
  (D.sp.X i).L0.map ((((D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm) :
      (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) :
      (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))

def badG : Set (HeightOneSpectrum (𝓞 D.host.F)) :=
  {v | (D.host.g 0 : 𝓞 D.host.F) ∈ v.asIdeal ∨ (D.host.g 1 : 𝓞 D.host.F) ∈ v.asIdeal}

abbrev PlT (u : D.what₂.Word) : Type :=
  {v : HeightOneSpectrum (𝓞 D.host.F) // (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}

abbrev Fr (i : ℕ) (hi : i ≤ D.R.m) : Type := Frames (gramC (gramN D i hi) (embT D))

def RatSpan {n : ℕ} (lam : D.what₂.Tau → DomWeight n) :
    AddSubgroup (MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) :=
  AddSubgroup.closure {p | ∃ (r : D.what₂.LL) (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ),
    (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = D.what₂.embLL r • ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}

def IntSpan {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) :
    AddSubgroup (MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) :=
  AddSubgroup.closure {p | ∃ (r : D.what₂.LL) (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ),
    r ∈ intW D.what₂.places w ∧ (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = D.what₂.embLL r • ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}

variable {D}

def lamT (u : D.what₂.Word) (i : ℕ) : D.what₂.Tau → DomWeight (D.R.N i) :=
  fun τ => shW ((D.fm u).lam i τ) ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)

theorem lamT_zero (u : D.what₂.Word) : lamT u 0 = (D.fm u).lam 0 := by
  funext τ
  simp [lamT, shW_zero]


set_option maxHeartbeats 1000000 in
structure ClsTied (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) where

  lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) (D.mem u).A.T D.R.f (badG D)

  y : (D.mem u).C.cls i → UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls lev))

  y_lat : ∀ c (x : Fin (D.R.N i) → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F))
      (clsCrd D u i hi c) ↔
    ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) lev.Lb

  stabI : ∀ c, (D.mem u).C.stab i c →* UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)),
    γ ∈ (stabI c).range ↔
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        lev.U.map (MulAut.conj (y c).1).toMonoidHom


set_option maxHeartbeats 1000000 in
structure ValTied (u : D.what₂.Word) (eV : (D.mem u).A.vT ≃ PlT D u) (i : ℕ) (hi : i ≤ D.R.m) (K : ClsTied u i hi) where

  eY : (D.mem u).C.Y i ≃ Fr D i hi

  de : ∃ C : GL (Fin (D.R.N i)) D.host.E,
    cT (sigD D : D.host.E →+* D.host.E) C.1 * C.1 = gramN D i hi ∧
    (∀ x : Fin (D.R.N i) → D.host.E, x ∈ selfDualLatticeCoords D i hi ↔ ∀ a, (C.1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) ∧
    ∀ τ z, (D.mem u).C.de i z τ = embT D τ C.1.det * ((eY z).1 τ).det

  Fi : ∀ φ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ, φ ∈ (D.fm u).Fi i ↔
    (fun c z => φ c (eY.symm z)) ∈ FiC K.lev (embT D) (lamT u i) K.y

  ipV : ∀ c (o : Fr D i hi), o.IsON → ∀ P ∈ CSpan ((D.fm u).lam i), ∀ Q ∈ CSpan ((D.fm u).lam i),
    (D.fm u).ipV i c
      (fun z => fnOf _ (shiftOf (lamT u i)) (fun τ => (o.1 τ)⁻¹) P (eY z))
      (fun z => fnOf _ (shiftOf (lamT u i)) (fun τ => (o.1 τ)⁻¹) Q (eY z)) =
    nfAll ((D.fm u).lam i) Q P

  rat : ∀ φ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ, (∃ x, (D.fm u).emb i x = φ) ↔
    φ ∈ (D.fm u).Fi i ∧ ∀ c, ∃ P ∈ RatSpan D ((D.fm u).lam i),
      ∀ z, φ c z = fnOf _ (shiftOf (lamT u i)) 1 P (eY z)

  lat : ∀ x : ((D.fm u).lat i).V, x ∈ ((D.fm u).lat i).L ↔
    ∀ (w : D.what₂.places.Pl) (c : (D.mem u).C.cls i) (B : GL (Fin (D.R.N i)) D.host.E),
      IsLocBasis (D.what₂.places.resChar w)
        (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (clsCrd D u i hi c)) B →
      ∃ P ∈ IntSpan D w ((D.fm u).lam i),
        ∀ z, (D.fm u).emb i x c z =
          fnOf _ (shiftOf (lamT u i)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) P (eY z)

  dil : ∀ v (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ), (k : (D.mem u).A.Fv v) = a → ∀ c δ,
    IsDia K.lev (eV v).1 (eV v).2 k δ →
    (Quotient.mk'' (K.y ((D.fm u).dil i v a c)) : Cls K.lev) = Quotient.mk'' (K.y c * δ)

  dilT : ∀ v (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ), (k : (D.mem u).A.Fv v) = a → ∀ c δ,
    IsDia K.lev (eV v).1 (eV v).2 k δ → ∀ g ∈ AdFun K.lev (embT D),
    (D.fm u).dilT i v a c (fun z => g (K.y ((D.fm u).dil i v a c)) (eY z)) = fun z => g (K.y c * δ) (eY z)

end Formalism.L2.Forms
end
end

