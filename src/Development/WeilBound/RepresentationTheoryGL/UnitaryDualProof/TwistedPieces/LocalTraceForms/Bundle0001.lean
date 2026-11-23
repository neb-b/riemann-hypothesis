module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.TraceForm
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.TraceCompSmulRight

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.LocChi
section
noncomputable section

open Matrix Polynomial GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.TP.Loc

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Split : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {m : ℕ} (F : Fin m → Set (Matrix (Fin n) (Fin n) k)),
    (∀ i, IsClosed (F i) ∧ ∀ g ∈ Gz Z, ∀ x ∈ F i, g.val * x * g⁻¹.val ∈ F i) → (∀ i j, i ≠ j → Disjoint (F i) (F j)) →
    ∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ ((⋃ i, F i) ×ˢ Set.univ) → Inv Z ξ →
      ∃ η : Fin m → (Sp k n → ℂ) →ₗ[ℂ] ℂ, (∀ i, Supp (η i) (F i ×ˢ Set.univ) ∧ Inv Z (η i)) ∧
        ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), ξ f = ∑ i, η i f

def LocChi : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (U : Set (Sp k n)), IsOpen U →
    (∀ χ : k[X], ∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ ((Bz Z ∩ {x | x.charpoly = χ}) ×ˢ Set.univ) → Inv Z ξ → Kills ξ U) →
    ∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ (Bz Z ×ˢ Set.univ) → Inv Z ξ → Kills ξ U

end PositivityTheory.RgUd.TP.Loc
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.Ptransl
section
noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.TP.Loc.Ptransl

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def trH (c : Matrix (Fin n) (Fin n) k) : Sp k n ≃ₜ Sp k n where
  toFun p := (p.1 - c, p.2)
  invFun p := (p.1 + c, p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := (continuous_fst.sub continuous_const).prodMk continuous_snd
  continuous_invFun := (continuous_fst.add continuous_const).prodMk continuous_snd

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem comp_mem {U V : Set (Sp k n)} (e : Sp k n ≃ₜ Sp k n) (hUV : ∀ p, e p ∈ U → p ∈ V) {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn U) : (fun p => f (e p)) ∈ supportedIn V := by
  obtain ⟨⟨hlc, hcs⟩, hsupp⟩ := hf
  refine ⟨⟨hlc.comp_continuous e.continuous, hcs.comp_homeomorph e⟩, ?_⟩
  intro p hp
  exact hUV p (hsupp hp)

theorem act_trH {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z)
    {g : GL (Fin n) k} (hg : g ∈ Gz Z) (p : Sp k n) : act g (trH c p) = trH c (act g p) := by
  have hcomm : c * (g : Matrix (Fin n) (Fin n) k) = g * c := hg c hc
  have hconj : (g : Matrix (Fin n) (Fin n) k) * c * (g⁻¹ : GL (Fin n) k) = c := by
    rw [← hcomm, Matrix.mul_assoc]
    simp
  simp only [act, trH, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, Prod.mk.injEq, and_true]
  rw [Matrix.mul_sub, Matrix.sub_mul, hconj]

theorem transl : Transl k := by
  intro m Z hCR hNB c hc F hF hnil ξ hsupp hinv
  let ξ' : (Sp k m → ℂ) →ₗ[ℂ] ℂ := ξ.comp (LinearMap.funLeft ℂ ℂ (trH c))
  have hξ' : ∀ f, ξ' f = ξ (fun p => f (trH c p)) := fun f => rfl
  have hmem : ∀ f ∈ supportedIn (Set.univ : Set (Sp k m)),
      (fun p => f (trH c p)) ∈ supportedIn (Set.univ : Set (Sp k m)) :=
    fun f hf => comp_mem (trH c) (fun _ _ => Set.mem_univ _) hf
  have hS : Supp ξ' (NB Z ×ˢ Set.univ) := by
    intro f hf hz
    rw [hξ']
    refine hsupp _ (hmem f hf) ?_
    rintro ⟨x, v⟩ ⟨hx, -⟩
    apply hz
    refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
    · intro a ha
      have h1 : a * x = x * a := hF hx a ha
      have h2 : a * c = c * a := hCR.1 a ha c hc
      change a * (x - c) = (x - c) * a
      rw [Matrix.mul_sub, Matrix.sub_mul, h1, h2]
    · exact hnil x hx
  have hI : T.Inv Z ξ' := by
    intro g hg f hf
    rw [hξ', hξ']
    have : (fun p => f (act g (trH c p))) = (fun p => (fun q => f (trH c q)) (act g p)) := by
      funext p
      rw [act_trH hc hg]
    rw [this]
    exact hinv g hg _ (hmem f hf)
  have hK := hNB ξ' hS hI
  intro f hf
  have hf' : (fun p => f ((trH c).symm p)) ∈ supportedIn {p : Sp k m | p.2 ≠ 0} :=
    comp_mem (trH c).symm (fun _ h => h) hf
  have := hK _ hf'
  rw [hξ'] at this
  simpa using this

end PositivityTheory.RgUd.TP.Loc.Ptransl
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.TraceFormCore
section
noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Loc.Ptf

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable {k : Type} [Field k] {n : ℕ}

def bSub (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Submodule k (Matrix (Fin n) (Fin n) k) where
  carrier := Bz Z
  add_mem' {x y} hx hy a ha := by rw [mul_add, add_mul, hx a ha, hy a ha]
  zero_mem' a _ := by simp
  smul_mem' c x hx a ha := by rw [mul_smul_comm, smul_mul_assoc, hx a ha]

theorem mul_mem_bz {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {x y : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z)
    (hy : y ∈ Bz Z) : x * y ∈ Bz Z := by
  intro a ha
  rw [← mul_assoc, hx a ha, mul_assoc, hy a ha, ← mul_assoc]

def RZ (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Type := Z

section Inst

variable (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z)

def crZ : CommRing (RZ Z) := { (inferInstance : Ring Z) with mul_comm := fun a b => Subtype.ext (hZ.1 _ a.2 _ b.2) }

def valZ : @RingHom (RZ Z) (Matrix (Fin n) (Fin n) k) (crZ Z hZ).toNonAssocSemiring _ :=
  letI := crZ Z hZ
  { toFun := fun z => (show Z from z).1
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl }

def algZ : @RingHom k (RZ Z) _ (crZ Z hZ).toNonAssocSemiring :=
  letI := crZ Z hZ
  { toFun := fun c => (show RZ Z from (⟨algebraMap k _ c, Z.algebraMap_mem c⟩ : Z))
    map_one' := Subtype.ext (map_one _)
    map_mul' := fun a b => Subtype.ext (map_mul (algebraMap k (Matrix (Fin n) (Fin n) k)) a b)
    map_zero' := Subtype.ext (map_zero _)
    map_add' := fun a b => Subtype.ext (map_add (algebraMap k (Matrix (Fin n) (Fin n) k)) a b) }

end Inst

theorem traceForm_core (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) :
    ∃ τ : Matrix (Fin n) (Fin n) k →ₗ[k] k,
      (∀ x ∈ Bz Z, ∀ y ∈ Bz Z, τ (x * y) = τ (y * x)) ∧ (∀ x ∈ Bz Z, (∀ y ∈ Bz Z, τ (x * y) = 0) → x = 0) ∧
        ∀ x ∈ NB Z, τ x = 0 := by
  letI : CommRing (RZ Z) := crZ Z hZ
  letI : Algebra k (RZ Z) := (algZ Z hZ).toAlgebra
  letI : Module (RZ Z) (Fin n → k) := Module.compHom (Fin n → k)
    ((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toRingEquiv.toRingHom.comp (valZ Z hZ))
  have hsmul : ∀ (r : RZ Z) (v : Fin n → k), r • v = (valZ Z hZ r) *ᵥ v := fun r v => rfl
  have hval : ∀ (c : k) (r : RZ Z), valZ Z hZ (c • r) = c • valZ Z hZ r := by
    intro c r
    rw [Algebra.smul_def, map_mul]
    show algebraMap k (Matrix (Fin n) (Fin n) k) c * valZ Z hZ r = _
    rw [Algebra.smul_def]
  haveI : IsScalarTower k (RZ Z) (Fin n → k) := ⟨fun c r v => by
    rw [hsmul, hsmul, hval, Matrix.smul_mulVec]⟩
  let L : RZ Z →ₗ[k] Matrix (Fin n) (Fin n) k :=
    { toFun := valZ Z hZ
      map_add' := map_add _
      map_smul' := hval }
  have hLinj : Function.Injective L := fun a b h => Subtype.ext h
  haveI : Module.Finite k (RZ Z) := Module.Finite.of_injective L hLinj
  haveI : IsArtinianRing (RZ Z) := IsArtinianRing.of_finite k (RZ Z)
  haveI : IsReduced (RZ Z) := hZ.2
  obtain ⟨τ0, hc, hnd, hnil⟩ := exists_tau (k := k) (R := RZ Z) (V := Fin n → k)
  have hcomm : ∀ x ∈ Bz Z, ∀ r : RZ Z, x * valZ Z hZ r = valZ Z hZ r * x :=
    fun x hx r => (hx _ (show Z from r).2).symm
  let ψ : bSub Z →ₗ[k] ((Fin n → k) →ₗ[RZ Z] (Fin n → k)) :=
    { toFun := fun x =>
        { toFun := fun v => x.1 *ᵥ v
          map_add' := fun v w => Matrix.mulVec_add _ _ _
          map_smul' := fun r v => by
            show x.1 *ᵥ (valZ Z hZ r *ᵥ v) = valZ Z hZ r *ᵥ (x.1 *ᵥ v)
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm x.1 x.2 r] }
      map_add' := fun x y => LinearMap.ext fun v => by
        show (x.1 + y.1) *ᵥ v = x.1 *ᵥ v + y.1 *ᵥ v
        exact Matrix.add_mulVec _ _ _
      map_smul' := fun c x => LinearMap.ext fun v => by
        show (c • x.1) *ᵥ v = c • (x.1 *ᵥ v)
        exact Matrix.smul_mulVec _ _ _ }
  have hψ : ∀ (x : bSub Z) (v : Fin n → k), ψ x v = x.1 *ᵥ v := fun x v => rfl
  have hψmul : ∀ x (hx : x ∈ Bz Z) y (hy : y ∈ Bz Z),
      ψ ⟨x * y, mul_mem_bz hx hy⟩ = ψ ⟨x, hx⟩ * ψ ⟨y, hy⟩ := by
    intro x hx y hy
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, hψ, hψ, hψ, Matrix.mulVec_mulVec]
  obtain ⟨τ, hτ⟩ := LinearMap.exists_extend (τ0.comp ψ)
  have hτx : ∀ x (hx : x ∈ Bz Z), τ x = τ0 (ψ ⟨x, hx⟩) := fun x hx =>
    LinearMap.congr_fun hτ ⟨x, hx⟩
  refine ⟨τ, ?_, ?_, ?_⟩
  · intro x hx y hy
    rw [hτx _ (mul_mem_bz hx hy), hτx _ (mul_mem_bz hy hx), hψmul x hx y hy, hψmul y hy x hx, hc]
  · intro x hx H
    have hsurj : ∀ g : (Fin n → k) →ₗ[RZ Z] (Fin n → k), ∃ y : bSub Z, ψ y = g := by
      intro g
      let y := LinearMap.toMatrix' (g.restrictScalars k)
      have hy : ∀ v, y *ᵥ v = g v := fun v => LinearMap.toMatrix'_mulVec _ _
      have hyB : y ∈ Bz Z := by
        intro a ha
        apply Matrix.toLin'.injective
        refine LinearMap.ext fun v => ?_
        rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec, hy, hy]
        exact (g.map_smul (show RZ Z from (⟨a, ha⟩ : Z)) v).symm
      exact ⟨⟨y, hyB⟩, LinearMap.ext fun v => hy v⟩
    have h0 : ψ ⟨x, hx⟩ = 0 := hnd _ fun g => by
      obtain ⟨y, rfl⟩ := hsurj g
      rw [← hψmul x hx y.1 y.2, ← hτx]
      exact H y.1 y.2
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply, ← hψ ⟨x, hx⟩, h0,
      LinearMap.zero_apply]
  · rintro x ⟨hx, m, hm⟩
    rw [hτx x hx]
    apply hnil
    refine ⟨m, LinearMap.ext fun v => ?_⟩
    have hpow : ∀ j : ℕ, (ψ ⟨x, hx⟩ ^ j) v = (x ^ j) *ᵥ v := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ', Module.End.mul_apply, ih, hψ, Matrix.mulVec_mulVec, pow_succ']
    rw [hpow, hm, LinearMap.zero_apply, Matrix.zero_mulVec]

theorem traceForm (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    TraceForm k := fun _ Z hZ => traceForm_core Z hZ

end PositivityTheory.RgUd.TP.Loc.Ptf
end
end

