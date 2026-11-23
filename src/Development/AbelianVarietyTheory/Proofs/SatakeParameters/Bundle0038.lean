module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0008
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleBranchingIffIsBranching
section
noncomputable section

namespace GlobalTheory.InertialTypesCmp

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open Formalism.MainNotions.SumRepresentations.At

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

open NumberField IsDedekindDomain Polynomial in
variable {R : _root_.Formalism.BasicNotions.Ranks} {H : _root_.Formalism.BasicNotions.Host R} {what₂ : _root_.Formalism.BasicNotions.Rows.Data R} (N : _root_.Formalism.BasicNotions.NData R H what₂) (A : _root_.Formalism.BasicNotions.NAut N) in
private theorem lpDim_foldr_lpSum_eq_sum_map {α : Type*} {w : _root_.Formalism.BasicNotions.PlE H}
    (f : α → A.LP w) (l : List α) :
    A.lpDim (l.foldr (fun k acc => A.lpSum (f k) acc) (A.lpZero w)) =
      (l.map fun k => A.lpDim (f k)).sum := by
  induction l with
  | nil => simp [_root_.Formalism.BasicNotions.NAut.lpDim_zero]
  | cons k l ih => simp [_root_.Formalism.BasicNotions.NAut.lpDim_sum, ih]

open NumberField IsDedekindDomain Polynomial in
variable {R : _root_.Formalism.BasicNotions.Ranks} {H : _root_.Formalism.BasicNotions.Host R} {what₂ : _root_.Formalism.BasicNotions.Rows.Data R} (N : _root_.Formalism.BasicNotions.NData R H what₂) (A : _root_.Formalism.BasicNotions.NAut N) in
private theorem lpDim_foldr_lpSum_eq_length_mul_of_const {α : Type*} {w : _root_.Formalism.BasicNotions.PlE H}
    (f : α → A.LP w) (m : ℕ) (hf : ∀ k, A.lpDim (f k) = m) (l : List α) :
    A.lpDim (l.foldr (fun k acc => A.lpSum (f k) acc) (A.lpZero w)) = l.length * m := by
  induction l with
  | nil => simp [_root_.Formalism.BasicNotions.NAut.lpDim_zero]
  | cons k l ih => simp [_root_.Formalism.BasicNotions.NAut.lpDim_sum, hf, ih, add_mul, add_comm]

open NumberField IsDedekindDomain Polynomial in
variable {R : _root_.Formalism.BasicNotions.Ranks} {H : _root_.Formalism.BasicNotions.Host R} {what₂ : _root_.Formalism.BasicNotions.Rows.Data R} (N : _root_.Formalism.BasicNotions.NData R H what₂) (A : _root_.Formalism.BasicNotions.NAut N) in
private theorem lpDim_spehLoc_eq_mul (p : _root_.Formalism.BasicNotions.Part A.CG) (w : _root_.Formalism.BasicNotions.PlE H) :
    A.lpDim (_root_.Formalism.MainNotions.N.spehLoc N A p w) = p.a * p.d := by
  unfold _root_.Formalism.MainNotions.N.spehLoc
  rw [lpDim_foldr_lpSum_eq_length_mul_of_const N A _ p.a (fun k => by rw [_root_.Formalism.BasicNotions.NAut.lpDim_tw, _root_.Formalism.BasicNotions.NAut.locG_dim])]
  simp [mul_comm]

open NumberField IsDedekindDomain Polynomial in
variable {R : _root_.Formalism.BasicNotions.Ranks} {H : _root_.Formalism.BasicNotions.Host R} {what₂ : _root_.Formalism.BasicNotions.Rows.Data R} (N : _root_.Formalism.BasicNotions.NData R H what₂) (A : _root_.Formalism.BasicNotions.NAut N) in
theorem _root_.GlobalTheory.InertialTypesCmp.lpDim_isoLoc (P : List (_root_.Formalism.BasicNotions.Part A.CG)) (w : _root_.Formalism.BasicNotions.PlE H) :
    A.lpDim (_root_.Formalism.MainNotions.N.isoLoc N A P w) = _root_.Formalism.MainNotions.N.rankIso N A P := by
  unfold _root_.Formalism.MainNotions.N.isoLoc _root_.Formalism.MainNotions.N.rankIso
  rw [lpDim_foldr_lpSum_eq_sum_map]
  simp [lpDim_spehLoc_eq_mul]

end GlobalTheory.InertialTypesCmp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DownMemRecOfTies
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowTie

theorem downMemRec_of_ties : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → GlobalTheory.RowCopy.ThetaOne D → Rows.IsotInternal D.what₂ → (∀ i, GlobalTheory.ThetaExh.PartOrth D.nd i) → (∀ i, GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.PairLift D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.BCEx D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.SplitBC D.nd D.naut i) → ∀ i, GlobalTheory.RowCopy.DownMemRec D.nd D.naut i :=
  fun D T hθ hI hO hT hP hB hS i =>
    GlobalTheory.DownMemRoad.downMem _ _ _ D.nd D.naut i hθ hI (hO i) (hT i) (_root_.GlobalTheory.RowLaws.main _ _ _ D.nd D.naut T).1
      (splitLift_of_pairLift _ _ _ D.nd D.naut i (hP i)) (_root_.GlobalTheory.RowTie.locOfPt_of_splitBC _ _ _ D.nd D.naut i (hB i) (hS i))

end GlobalTheory.RowTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsConjDoubleBlockOfIsoSubspaces
section
open Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.DoubleBlock

open Matrix

variable {k Γ : Type} [Field k] [Group Γ] {a : ℕ}

theorem exists_emb (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) (hW : IsInv ρ W) :
    ∃ (σ : Γ →* GL (Fin (Module.finrank k W)) k) (φ : (Fin (Module.finrank k W) → k) ≃ₗ[k] W),
      ∀ g x, (φ ((σ g : Matrix _ _ k) *ᵥ x) : Fin a → k) = (ρ g : Matrix _ _ k) *ᵥ (φ x : Fin a → k) := by
  classical
  let φ : (Fin (Module.finrank k W) → k) ≃ₗ[k] W := (Module.finBasis k W).equivFun.symm
  let r : Γ → (W →ₗ[k] W) := fun g =>
    (Matrix.toLin' (ρ g : Matrix (Fin a) (Fin a) k)).restrict (p := W) (q := W) (fun v hv => hW g v hv)
  have hr : ∀ g v, (r g v : Fin a → k) = (ρ g : Matrix _ _ k) *ᵥ (v : Fin a → k) := fun g v => rfl
  let m : Γ →* Matrix (Fin (Module.finrank k W)) (Fin (Module.finrank k W)) k :=
    { toFun := fun g => LinearMap.toMatrix' (φ.symm.toLinearMap ∘ₗ r g ∘ₗ φ.toLinearMap)
      map_one' := by
        rw [← LinearMap.toMatrix'_id]
        congr 1
        apply LinearMap.ext
        intro x
        have : r 1 (φ x) = φ x := by
          apply Subtype.ext
          rw [hr]; simp
        simp [this]
      map_mul' := fun g h => by
        rw [← LinearMap.toMatrix'_comp]
        congr 1
        apply LinearMap.ext
        intro x
        have : r (g * h) (φ x) = r g (r h (φ x)) := by
          apply Subtype.ext
          rw [hr, hr, hr]; simp
        simp [this] }
  refine ⟨m.toHomUnits, φ, fun g x => ?_⟩
  have : ((m.toHomUnits g : Matrix _ _ k)) *ᵥ x = φ.symm (r g (φ x)) := by
    change LinearMap.toMatrix' (φ.symm.toLinearMap ∘ₗ r g ∘ₗ φ.toLinearMap) *ᵥ x = _
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  rw [this, LinearEquiv.apply_symm_apply, hr]

theorem exists_emb_sum (ρ : Γ →* GL (Fin a) k) {d u : ℕ} (σ : Γ →* GL (Fin d) k)
    (τ : Γ →* GL (Fin u) k) (f₁ : (Fin d → k) →ₗ[k] (Fin a → k))
    (f₂ : (Fin u → k) →ₗ[k] (Fin a → k)) (i₁ : Function.Injective f₁) (i₂ : Function.Injective f₂)
    (h₁ : ∀ g x, f₁ ((σ g : Matrix _ _ k) *ᵥ x) = (ρ g : Matrix _ _ k) *ᵥ f₁ x)
    (h₂ : ∀ g x, f₂ ((τ g : Matrix _ _ k) *ᵥ x) = (ρ g : Matrix _ _ k) *ᵥ f₂ x)
    (hd : Disjoint (LinearMap.range f₁) (LinearMap.range f₂)) :
    ∃ f : (Fin (d + u) → k) →ₗ[k] (Fin a → k), Function.Injective f ∧
      LinearMap.range f = LinearMap.range f₁ ⊔ LinearMap.range f₂ ∧
      ∀ g x, f ((SumRepresentations.At.sumRep σ τ g : Matrix _ _ k) *ᵥ x) = (ρ g : Matrix _ _ k) *ᵥ f x := by
  let s : (Fin (d + u) → k) ≃ₗ[k] (Fin d → k) × (Fin u → k) :=
    (LinearEquiv.funCongrLeft k k finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow _ _ k k)
  have hs : ∀ x, s x = (fun i => x (finSumFinEquiv (Sum.inl i)), fun i => x (finSumFinEquiv (Sum.inr i))) :=
    fun x => rfl
  refine ⟨(f₁.coprod f₂) ∘ₗ s.toLinearMap, ?_, ?_, fun g x => ?_⟩
  · have : Function.Injective (f₁.coprod f₂) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range _ _ hd,
        LinearMap.ker_eq_bot.2 i₁, LinearMap.ker_eq_bot.2 i₂, Submodule.prod_bot]
    exact this.comp s.injective
  · rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, LinearMap.range_coprod]
  · have key : s ((SumRepresentations.At.sumRep σ τ g : Matrix _ _ k) *ᵥ x) =
        ((σ g : Matrix _ _ k) *ᵥ (s x).1, (τ g : Matrix _ _ k) *ᵥ (s x).2) := by
      have hM : (SumRepresentations.At.sumRep σ τ g).val = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (σ g).val 0 0 (τ g).val) := rfl
      rw [hM, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, hs, hs]
      ext i <;> simp [Function.comp_def]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, key, LinearMap.coprod_apply, h₁, h₂,
      Matrix.mulVec_add]

theorem exists_conj (ρ : Γ →* GL (Fin a) k) {n : ℕ} (τ : Γ →* GL (Fin n) k)
    (f : (Fin n → k) →ₗ[k] (Fin a → k)) (hi : Function.Injective f) (hs : LinearMap.range f = ⊤)
    (h : ∀ g x, f ((τ g : Matrix _ _ k) *ᵥ x) = (ρ g : Matrix _ _ k) *ᵥ f x) :
    ∃ (hn : n = a) (Pm : GL (Fin a) k), ∀ g,
      ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
        Matrix.reindex (finCongr hn) (finCongr hn) ((τ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  classical
  let e := LinearEquiv.ofBijective f ⟨hi, LinearMap.range_eq_top.1 hs⟩
  have hn : n = a := by simpa using e.finrank_eq
  subst hn
  let Pm : GL (Fin n) k := ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hP : ∀ x, (Pm : Matrix _ _ k) *ᵥ x = f x := fun x => LinearMap.toMatrix'_mulVec _ _
  refine ⟨rfl, Pm, fun g => ?_⟩
  have : ρ g * Pm = Pm * τ g := by
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Units.val_mul, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hP, h]
  rw [mul_assoc, this, inv_mul_cancel_left]
  simp

theorem exists_conj_double : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W₁ W₂ : Submodule k (Fin a → k)), IsSSRep ρ → IsInv ρ W₁ → IsInv ρ W₂ → W₁ ≠ ⊥ → W₁ ⊓ W₂ = ⊥ → IsoSub ρ W₁ W₂ → ∃ (d u : ℕ) (σ : Γ →* GL (Fin d) k) (υ : Γ →* GL (Fin u) k) (h : d + d + u = a) (Pm : GL (Fin a) k), 0 < d ∧ ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) = Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) k) : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k) := by
  intro k Γ _ _ a ρ W₁ W₂ hss h₁ h₂ hne hdis ⟨e, he⟩
  have h12 : IsInv ρ (W₁ ⊔ W₂) := by
    intro g v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem_sup (h₁ g x hx) (h₂ g y hy)
  obtain ⟨U, hU, hc⟩ := hss _ h12
  obtain ⟨σ, φ, hφ⟩ := exists_emb ρ W₁ h₁
  obtain ⟨υ, ψ, hψ⟩ := exists_emb ρ U hU
  have r₁ : LinearMap.range (W₁.subtype ∘ₗ φ.toLinearMap) = W₁ := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have r₂ : LinearMap.range (W₂.subtype ∘ₗ (φ.trans e).toLinearMap) = W₂ := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have r₃ : LinearMap.range (U.subtype ∘ₗ ψ.toLinearMap) = U := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨f, fi, fr, hf⟩ := exists_emb_sum ρ σ σ (W₁.subtype ∘ₗ φ.toLinearMap)
    (W₂.subtype ∘ₗ (φ.trans e).toLinearMap) (W₁.injective_subtype.comp φ.injective)
    (W₂.injective_subtype.comp (φ.trans e).injective) (fun g x => hφ g x)
    (fun g x => by
      have := he g (φ x) (h₁ g _ (φ x).2)
      have h' : φ ((σ g : Matrix _ _ k) *ᵥ x) = ⟨_, h₁ g _ (φ x).2⟩ := Subtype.ext (hφ g x)
      change (e (φ ((σ g : Matrix _ _ k) *ᵥ x)) : Fin a → k) = _
      rw [h', this]
      rfl)
    (by rw [r₁, r₂]; exact disjoint_iff.2 hdis)
  rw [r₁, r₂] at fr
  obtain ⟨F, Fi, Fr, hF⟩ := exists_emb_sum ρ (SumRepresentations.At.sumRep σ σ) υ f (U.subtype ∘ₗ ψ.toLinearMap) fi
    (U.injective_subtype.comp ψ.injective) hf (fun g x => hψ g x)
    (by rw [fr, r₃]; exact hc.disjoint)
  rw [fr, r₃, hc.sup_eq_top] at Fr
  obtain ⟨hn, Pm, hP⟩ := exists_conj ρ _ F Fi Fr hF
  exact ⟨_, _, σ, υ, hn, Pm, Nat.pos_of_ne_zero (fun h0 => hne (Submodule.finrank_eq_zero.1 h0)), hP⟩

end GlobalTheory.DoubleBlock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomOfIsStrictHenselisation
section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing

noncomputable section
namespace GlobalTheory.NCyc.StrictLocLift

theorem lift_unique {R Q T : Type} [CommRing R] [CommRing Q] [CommRing T] [HenselianLocalRing T]
    (tQ : R →+* Q) (htQ : tQ.Etale) (b : R →+* T) (g₁ g₂ : Q →+* T)
    (h₁ : g₁.comp tQ = b) (h₂ : g₂.comp tQ = b)
    (h : (residue T).comp g₁ = (residue T).comp g₂) : g₁ = g₂ := by
  letI : Algebra R Q := tQ.toAlgebra
  letI : Algebra R T := b.toAlgebra
  haveI : Algebra.Etale R Q := htQ
  let G₁ : Q →ₐ[R] T := { g₁ with commutes' := fun r => DFunLike.congr_fun h₁ r }
  let G₂ : Q →ₐ[R] T := { g₂ with commutes' := fun r => DFunLike.congr_fun h₂ r }
  have := (GlobalTheory.EtaleHensel.bijective_residue_comp R Q T).1 (a₁ := G₁) (a₂ := G₂) (by
    ext q; exact DFunLike.congr_fun h q)
  ext q; exact DFunLike.congr_fun this q

theorem lift_exists {R Q T : Type} [CommRing R] [CommRing Q] [CommRing T] [HenselianLocalRing T]
    (tQ : R →+* Q) (htQ : tQ.Etale) (b : R →+* T) (ψ : Q →+* ResidueField T)
    (hψ : ψ.comp tQ = (residue T).comp b) :
    ∃ g : Q →+* T, g.comp tQ = b ∧ (residue T).comp g = ψ := by
  letI : Algebra R Q := tQ.toAlgebra
  letI : Algebra R T := b.toAlgebra
  haveI : Algebra.Etale R Q := htQ
  let Ψ : Q →ₐ[R] ResidueField T := { ψ with commutes' := fun r => DFunLike.congr_fun hψ r }
  obtain ⟨G, hG⟩ := (GlobalTheory.EtaleHensel.bijective_residue_comp R Q T).2 Ψ
  refine ⟨G.toRingHom, RingHom.ext fun r => G.commutes r, RingHom.ext fun q => ?_⟩
  exact DFunLike.congr_fun hG q

end GlobalTheory.NCyc.StrictLocLift

namespace GlobalTheory.NCyc.StrictLocLift

theorem exists_ringHom_of_isIndEtale {R S T : Type} [CommRing R] [CommRing S] [CommRing T] [HenselianLocalRing T]
    (a : R →+* S) (b : R →+* T) (ha : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale a) (ψ : S →+* ResidueField T)
    (hψ : ψ.comp a = (residue T).comp b) : ∃ g : S →+* T, g.comp a = b := by
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := ha
  have hts' : ∀ j, (s.app j).hom.comp (t.app j).hom = a := fun j => by
    have := congrArg CommRingCat.Hom.hom (hts j).2
    simpa using this
  have hψj : ∀ j, (ψ.comp (s.app j).hom).comp (t.app j).hom = (residue T).comp b := fun j => by
    rw [RingHom.comp_assoc, hts' j, hψ]
  choose g hg using fun j => lift_exists (t.app j).hom (hts j).1 b (ψ.comp (s.app j).hom) (hψj j)
  have nat : ∀ {j k : J} (u : j ⟶ k), (g k).comp (D.map u).hom = g j := by
    intro j k u
    have ht : (D.map u).hom.comp (t.app j).hom = (t.app k).hom := by
      have := congrArg CommRingCat.Hom.hom (t.naturality u)
      simpa using this.symm
    have hs' : (s.app k).hom.comp (D.map u).hom = (s.app j).hom := by
      have e : D.map u ≫ s.app k = s.app j := by
        have := s.naturality u
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
        exact this
      have := congrArg CommRingCat.Hom.hom e
      rwa [CommRingCat.hom_comp] at this
    apply lift_unique (t.app j).hom (hts j).1 b
    · rw [RingHom.comp_assoc, ht, (hg k).1]
    · exact (hg j).1
    · rw [← RingHom.comp_assoc, (hg k).2, RingHom.comp_assoc, hs', (hg j).2]
  let c : Cocone D :=
    { pt := CommRingCat.of T
      ι := { app := fun j => CommRingCat.ofHom (g j)
             naturality := fun j k u => by
               ext q
               simpa using DFunLike.congr_fun (nat u) q } }
  refine ⟨(hs.desc c).hom, ?_⟩
  obtain ⟨j⟩ : Nonempty J := IsFiltered.nonempty
  have hf : (hs.desc c).hom.comp (s.app j).hom = g j := by
    have := congrArg CommRingCat.Hom.hom (hs.fac c j)
    simpa [c] using this
  rw [← hts' j, ← RingHom.comp_assoc, hf, (hg j).1]

end GlobalTheory.NCyc.StrictLocLift

namespace GlobalTheory.NCyc.StrictLocLift

theorem exists_ringHom_of_isStrictHenselisation {R S T : Type} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] [CommRing T] [HenselianLocalRing T] [IsSepClosed (ResidueField T)]
    (a : R →+* S) (ha : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation a) (b : R →+* T) [IsLocalHom b] :
    ∃ g : S →+* T, g.comp a = b := by
  letI : Algebra R S := a.toAlgebra
  haveI : IsLocalHom (algebraMap R S) := ha.2.2.1
  obtain ⟨-, -, hsep⟩ := GlobalTheory.IndEtaleLocal.flat_map_maximalIdeal_isSeparable R S ha.2.2.2
  letI : Algebra (ResidueField R) (ResidueField T) := (ResidueField.map b).toAlgebra
  let ι : ResidueField S →ₐ[ResidueField R] ResidueField T := IsSepClosed.lift
  refine exists_ringHom_of_isIndEtale a b ha.2.2.2 (ι.toRingHom.comp (residue S)) (RingHom.ext fun r => ?_)
  have h1 : residue S (a r) = algebraMap (ResidueField R) (ResidueField S) (residue R r) := rfl
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [h1, ι.commutes]
  rfl

end GlobalTheory.NCyc.StrictLocLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPartRecursion
section
namespace GlobalTheory.Proof.GoodComponentRecursion

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem goodPartRec_of_ties : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → GlobalTheory.RowCopy.ThetaOne D →
    (∀ i, GlobalTheory.ThetaExh.LiftParam D.nd D.naut i) → (∀ i, GlobalTheory.ThetaExh.PtLocal D.nd D.naut i) →
    (∀ i, GlobalTheory.RowTie.BCEx D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.SplitBC D.nd D.naut i) →
    ∀ i, GlobalTheory.RowCopy.GoodPartRec D.nd D.naut i := by
  intro D hW h1 hlift hpt hbc hsp i
  exact GlobalTheory.Proof.SplitPlaceGoodSignature.goodPart_of_lifts D.nd D.naut i h1
    (_root_.GlobalTheory.RowLaws.main _ _ _ D.nd D.naut hW).1 (hlift i) (hpt i)
    (_root_.GlobalTheory.RowTie.locOfPt_of_splitBC _ _ _ D.nd D.naut i (hbc i) (hsp i))

end GlobalTheory.Proof.GoodComponentRecursion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisLocalWeights
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NRows

open Pointwise

theorem ine_conj_of_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {g σ : G F Ω} (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  have m : ∀ y : Ω, y ∈ g • A ↔ (g⁻¹ : G F Ω) y ∈ A := fun y => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  have m' : ∀ y : Ω, (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : G F Ω) y) < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', m, m, map_inv₀,
      map_eq_zero_iff _ (g⁻¹ : G F Ω).injective]
  have c : ∀ x : Ω, (g⁻¹ : G F Ω) (g x) = x := fun x => by
    show (g⁻¹ * g) x = x
    simp
  refine ⟨?_, fun x hx => ?_⟩
  · have h : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, m, c]
      exact (A.valuation_le_one_iff x).1 hx
    have h := (m' _).1 (hσ.2 _ hx')
    rw [map_sub, c] at h
    exact h

theorem crys_unram_of_lgc : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → (∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))), (∀ x, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) (r x))) → (∀ w ∈ placesOver D.host.E (D.nd.l i),
      (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → ∀ x, D.naut.IsCrysW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
        ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) ∧
      ((D.nd.l i = D.host.g 0 ∨ D.nd.l i = D.host.g 1) → ∀ x,
        (∀ P Pa, D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → D.naut.mono0 (isoLoc D.nd D.naut Pa w)) →
        D.naut.IsPotCrysW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w)) ∧
    ∀ x w, w ∉ placesOver D.host.E (D.nd.l i) → w ∉ D.nd.S i → w ∉ D.nd.Q i → UnramAt (F := D.host.E) (r x) w := by
  intro D htie hadm hLGC i r hr
  obtain ⟨-, -, hGal⟩ := htie
  have hl : (D.nd.l i).Prime := Fact.out
  have key : ∀ x, ∃ P Pa, D.naut.ptV i P = some x ∧ IsBCV D.nd D.naut i P Pa := fun x => by
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := hadm i P
    exact ⟨P, Pa, hP, hPa⟩
  have hunr : ∀ P Pa w, IsBCV D.nd D.naut i P Pa → w ∉ D.nd.Q i →
      (∀ k, w ∉ placesOver D.host.E (D.host.g k)) →
      w ∉ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) →
      D.naut.unr (isoLoc D.nd D.naut Pa w) := by
    intro P Pa w hB hQ hg hp
    by_cases hs : IsSplitPl D.host w
    · rw [hB.2.2.2.1 w hs]
      exact D.naut.locV_unr i P w hs hQ hg hp
    · exact (hB.2.2.2.2.1 w hs).1
  refine ⟨fun w hw => ⟨fun hl0 hl1 x => ?_, fun _ x hm => ?_⟩, fun x w hwl hwS hwQ => ?_⟩
  · obtain ⟨P, Pa, hP, hB⟩ := key x
    have h := (hLGC i x P Pa hP hB _ (hr x)).2 w hw
    refine ⟨(hGal.1 i _ _ w hw (hr x).1).2 ⟨h.1, ?_⟩, fun τ hτ => h.2.2 τ hτ⟩
    rw [h.2.1, D.naut.unr_tw]
    refine hunr P Pa w hB (fun hq => D.nd.SQ_l i w (Or.inr hq) hw) (fun k => ?_) ?_
    · have hk : D.nd.l i ≠ D.host.g k := by
        fin_cases k
        · exact hl0
        · exact hl1
      exact SumRepresentations.not_over_of_ne hl (D.host.g_prime k) hk hw
    · split_ifs with hpd
      · exact SumRepresentations.not_over_of_ne hl D.host.pde'_prime (hpd ▸ D.host.pde_ne) hw
      · exact SumRepresentations.not_over_of_ne hl D.host.pde_prime hpd hw
  · obtain ⟨P, Pa, hP, hB⟩ := key x
    have h := (hLGC i x P Pa hP hB _ (hr x)).2 w hw
    refine (hGal.2.1 i _ _ w hw (hr x).1).2 ⟨h.1, ?_⟩
    rw [h.2.1, D.naut.monomial_twist_iff]
    exact hm P Pa hP hB
  · obtain ⟨P, Pa, hP, hB⟩ := key x
    have h := (hLGC i x P Pa hP hB _ (hr x)).1 w hwl
    have hS : ¬ ((w ∈ placesOver D.host.E (D.host.g 0) ∨ w ∈ placesOver D.host.E (D.host.g 1) ∨
        w ∈ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde)) ∧
        w ∉ placesOver D.host.E (D.nd.l i)) := fun hh => hwS ((D.nd.S_def i w).2 hh)
    have hu : D.naut.unr (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) := by
      rw [h, D.naut.unr_tw]
      refine hunr P Pa w hB hwQ (fun k hk => hS ⟨?_, hwl⟩) (fun hk => hS ⟨Or.inr (Or.inr hk), hwl⟩)
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
    have h1 := (D.naut.wdOf_unr i _ w hwl (hr x).1).1 hu
    intro A hA σ hσ
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (D.nd.plOm.2 w) hA
    have hσ' : σ ∈ Ine (F := D.host.E) (g • D.nd.plOm.1 w) := by rw [hg]; exact hσ
    have h2 := h1 _ (ine_conj_of_smul hσ')
    have h3 : mapRep (iotaOQ D.nd D.naut i) (r x) σ = 1 := by
      have e : σ = g * (g⁻¹ * σ * g) * g⁻¹ := by group
      rw [e, map_mul, map_mul, h2, mul_one, ← map_mul, mul_inv_cancel, map_one]
    apply Units.ext
    have h4 := congrArg (fun u : GL (Fin D.R.nV) (Qbar (D.nd.l i)) => u.val) h3
    simp only [mapRep, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one] at h4
    refine Matrix.map_injective (SumRepresentations.iotaOQ_injective D.nd D.naut i) ?_
    show (r x σ).val.map (iotaOQ D.nd D.naut i) = (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (iotaOQ D.nd D.naut i)
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact h4

end GlobalTheory.NRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweDualityUpwardOfLocalThetaSplitPlaces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowTie

theorem howeUp_of_pairLift : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GlobalTheory.RowTie.PairLift N A i → GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i →
    GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.HoweUp N A i := by
  intro R H what₂ N A i hL hB hS hR σ P P' hP hP'
  refine _root_.GlobalTheory.RowTie.repDet_split R H what₂ N A i hB hS hR P P' (Filter.Eventually.of_forall fun w hw => ?_)
  rw [hL σ P hP w hw, hL σ P' hP' w hw]

end GlobalTheory.RowTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceExtendsToIso
section
namespace GlobalTheory.ThLoc

theorem place_extends_to_iso : Formalism.L2.KerInert.LamExt :=
  fun p _ lam => GlobalTheory.PadicComplexIso.exists_ringEquiv_extending p lam

end GlobalTheory.ThLoc
end

