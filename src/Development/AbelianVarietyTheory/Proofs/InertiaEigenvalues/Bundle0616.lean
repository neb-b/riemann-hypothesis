module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0611
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0571
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0612
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfRootsBarEq
section
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.SerLocal

variable (D : D7)

theorem inePol_zero (w : PlE D.host) (s) (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (D.naut.lpZero w) s = 1 := by
  rw [((D.naut.unr_iff_ine _).1 (D.naut.lpZero_unr w)).2 s hs, D.naut.lpDim_zero, pow_zero]

theorem inePol_foldr {ι : Type} {w : PlE D.host} (F : ι → D.naut.LP w) (l : List ι) (s)
    (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (l.foldr (fun x acc => D.naut.lpSum (F x) acc) (D.naut.lpZero _)) s =
      (l.map fun x => D.naut.inePol (F x) s).prod := by
  induction l with
  | nil => simpa using inePol_zero D w s hs
  | cons x l ih => rw [List.foldr_cons, D.naut.inePol_sum, ih, List.map_cons, List.prod_cons]

theorem inePol_speh (p : Part D.naut.CG) (w : PlE D.host) (s)
    (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (spehLoc D.nd D.naut p w) s = D.naut.inePol (D.naut.locG p.π w) s ^ p.d := by
  have e : spehLoc D.nd D.naut p w = (List.range p.d).foldr (fun (j : ℕ) acc =>
      D.naut.lpSum (D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - j)) acc) (D.naut.lpZero w) := by
    simp only [spehLoc, bind_pure_comp, List.map_eq_map, List.foldr_map]
  rw [e, inePol_foldr D (fun k : ℕ => D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - k)) _ s hs]
  simp [D.naut.inePol_tw _ _ s hs]

theorem inePol_iso (P : List (Part D.naut.CG)) (w : PlE D.host) (s)
    (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (isoLoc D.nd D.naut P w) s =
      (P.map fun p => D.naut.inePol (D.naut.locG p.π w) s ^ p.d).prod := by
  rw [isoLoc, inePol_foldr D (fun p => spehLoc D.nd D.naut p w) _ s hs]
  simp only [inePol_speh D _ w s hs]

theorem inePol_twist (hU : IneUnr D) (i : D.nd.Loc) (Sig : List (Part D.naut.CG)) (w : PlE D.host) (s)
    (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (isoLoc D.nd D.naut
      (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) w) s =
      D.naut.inePol (isoLoc D.nd D.naut Sig w) s * D.naut.inePol (D.naut.locG (D.naut.muC i) w) s ^ D.R.t := by
  rw [inePol_iso D _ w s hs, inePol_iso D _ w s hs, twistIso, List.map_map]
  have e : ∀ {a} (π : D.naut.CG a), D.naut.inePol (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) s =
      D.naut.inePol (D.naut.locG π w) s := fun π => by
    rw [D.naut.locG_tw]
    exact hU w _ _ (D.naut.locG_dim _ w) (D.naut.etaTinv_def w).1 s hs
  simp [Function.comp_def, e, muPart]

section Roots

variable {g : ℕ} [Fact g.Prime]

theorem eq_of_rootsBar_eq {f f' : (ZMod g)[X]} (hf : f.Monic) (hf' : f'.Monic)
    (h : Formalism.CyclotomicNorms.rootsBar f = Formalism.CyclotomicNorms.rootsBar f') : f = f' := by
  apply Polynomial.map_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) (RingHom.injective _)
  rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (hf.map _),
    (IsAlgClosed.splits (f'.map _)).eq_prod_roots_of_monic (hf'.map _)]
  exact congrArg (fun m => (Multiset.map (fun x => X - C x) m).prod) h

theorem rootsBar_pow (c : ZMod g) (t : ℕ) :
    Formalism.CyclotomicNorms.rootsBar ((X - C c) ^ t) = t • {algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c} := by
  rw [Formalism.CyclotomicNorms.rootsBar, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C, roots_pow, roots_X_sub_C]

theorem eq_of_teich (τ : Formalism.CyclotomicNorms.Fbar g →* ℂ) (hτ : Function.Injective τ) {f f' : (ZMod g)[X]} (hf : f.Monic)
    (hf' : f'.Monic) (c : ZMod g) (t : ℕ)
    (h : ((Formalism.CyclotomicNorms.rootsBar (f * (X - C c) ^ t)).map fun x => X - C (τ x)).prod =
      ((Formalism.CyclotomicNorms.rootsBar f').map fun x => X - C (τ x)).prod *
        (X - C (τ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c))) ^ t) : f = f' := by
  have h0 : f * (X - C c) ^ t ≠ 0 := (hf.mul ((monic_X_sub_C c).pow t)).ne_zero
  have hm : Formalism.CyclotomicNorms.rootsBar (f * (X - C c) ^ t) = Formalism.CyclotomicNorms.rootsBar f + Formalism.CyclotomicNorms.rootsBar ((X - C c) ^ t) := by
    unfold Formalism.CyclotomicNorms.rootsBar
    rw [Polynomial.map_mul, roots_mul]
    rw [← Polynomial.map_mul]
    exact Polynomial.map_ne_zero h0
  rw [hm, rootsBar_pow, Multiset.map_add (f := _), Multiset.prod_add, Multiset.map_nsmul, Multiset.prod_nsmul,
    Multiset.map_singleton, Multiset.prod_singleton] at h
  have h2 := mul_right_cancel₀ (pow_ne_zero t (X_sub_C_ne_zero _)) h
  have h3 := congrArg Polynomial.roots h2
  have e : ∀ m : Multiset (Formalism.CyclotomicNorms.Fbar g),
      ((m.map fun x => X - C (τ x)).prod).roots = m.map τ := fun m => by
    rw [← roots_multiset_prod_X_sub_C (m.map τ), Multiset.map_map]; rfl
  rw [e, e] at h3
  exact eq_of_rootsBar_eq hf hf' (Multiset.map_injective hτ h3)

end Roots

theorem serLoc : ∀ (D : D7) (S : ∀ k, @Sys (D.host.g k) ⟨D.host.g_prime k⟩),
    (∀ k f, D.ntypes.eSer k f = @Sys.e _ ⟨D.host.g_prime k⟩ (S k) D.R.r f) → IneUnr D → LocType D S →
    SerLoc D := by
  intro D S hS hU hL i σ' k v f F hF hne
  letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hex : ∃ P Sig, (∀ w, isoLoc D.nd D.naut Sig w = D.ntypes.locPar σ' w) ∧
      IsBCV D.nd D.naut i P (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) ∧
      ∃ F' ∈ D.naut.typeV i P,
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (atPlace D k v (D.ntypes.eSer k f)) F' ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hne
    rw [D.mtpar_tie i σ'] at hF
    have hle : (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc D.nd D.naut Sig w = D.ntypes.locPar σ' w) ∧
        IsBCV D.nd D.naut i P (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv)},
        D.naut.typeV i P) ≤
        LinearMap.ker (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (atPlace D k v (D.ntypes.eSer k f))) :=
      iSup₂_le fun P ⟨Sig, h1, h2⟩ F' hF' => hno P Sig h1 h2 F' hF'
    exact hle hF
  obtain ⟨P, Sig, hSig, hBC, F', hF', hne'⟩ := hex
  obtain ⟨π, χ, c, h1, h2, h3, h4⟩ := hL i P k v
  obtain ⟨u, hu, hu'⟩ := h1 F' hF' (D.ntypes.eSer k f)
    (Subalgebra.mem_center_iff.2 fun b => (D.ntypes.eSer_central k f b).symm) hne'
  rw [hS] at hu'
  have hmon : f.Monic := ((S k).label D.R.r f (fun h0 => hu' (by rw [h0]; simp [actTop]))).1
  have hHas := _root_.GlobalTheory.SerSys.ParVec.has_mul_of_isParVec _ (S k) _ _ π.ρ D.R.r D.R.t χ _ f u rfl h2 hu hu'
  have h5 := h4 _ hHas
  have hs := D.ntypes.tg_mem k v
  rw [← hBC.2.2.2.1 _ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v), inePol_twist D hU i Sig _ _ hs, hSig, h3,
    D.ntypes.inertiaCharpoly_type k v _ (by
      rw [← D.ntypes.labPar_def, (D.ntypes.labPar_monic k σ' v).2, D.ntypes.locPar_dim]),
    ← D.ntypes.labPar_def] at h5
  exact eq_of_teich _ (GlobalTheory.TameLabels.teich_injective _ (D.ntypes.teichC_inj k)) hmon (D.ntypes.labPar_monic k σ' v).1 c _ h5.symm

end GlobalTheory.SerLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContractNeZero
section
noncomputable section

namespace GlobalTheory.SmGL.DepthZero

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.StepData ValuativeRel
open scoped TensorProduct

section Tensor

variable {α : Type} [Fintype α] [dec : DecidableEq α] {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

def contract (φ : ∀ a, X a →ₗ[ℂ] ℂ) (a : α) : (⨂[ℂ] b, X b) →ₗ[ℂ] X a := GlobalTheory.MultilinearContraction.contract φ a

theorem contract_tprod (φ : ∀ a, X a →ₗ[ℂ] ℂ) (a : α) (x : ∀ b, X b) :
    contract φ a (PiTensorProduct.tprod ℂ x) = (∏ b ∈ Finset.univ.erase a, φ b (x b)) • x a :=
  GlobalTheory.MultilinearContraction.contract_tprod φ a x

theorem exists_contract_ne_zero {w : ⨂[ℂ] b, X b} (hw : w ≠ 0) (a : α) :
    ∃ φ : ∀ a, X a →ₗ[ℂ] ℂ, contract φ a w ≠ 0 := by
  let b := fun i => Module.Free.chooseBasis ℂ (X i)
  let B := Basis.piTensorProduct b
  obtain ⟨p, hp⟩ : ∃ p, B.repr w p ≠ 0 := by
    by_contra! h
    exact hw (B.repr.injective (by ext p; simp [h p]))
  refine ⟨fun i => (b i).coord (p i), fun h => hp ?_⟩
  have key : (b a).coord (p a) ∘ₗ contract (fun i => (b i).coord (p i)) a = B.coord p := by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, contract_tprod, map_smul,
      Module.Basis.coord_apply, B, Basis.piTensorProduct_repr_tprod_apply, smul_eq_mul]
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
  have := congrArg (fun L => L w) key
  simp only [LinearMap.comp_apply, h, map_zero, Module.Basis.coord_apply] at this
  exact this.symm

theorem contract_piTensor {Γ : α → Type} [∀ a, Group (Γ a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (φ : ∀ a, X a →ₗ[ℂ] ℂ) (a : α) (g : Γ a) (w : ⨂[ℂ] b, X b) :
    contract φ a (piTensor ρ (Pi.mulSingle a g) w) = ρ a g (contract φ a w) := by
  induction w using PiTensorProduct.induction_on with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | smul_tprod c x =>
    simp only [map_smul, piTensor_tprod, contract_tprod, Pi.mulSingle_eq_same]
    congr 2
    exact Finset.prod_congr rfl fun b hb => by
      rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hb)]; simp

end Tensor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem isCompact_KOne₁ : IsCompact (KOne k n : Set (GL n k)) :=
  SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ isOpen_KOne) KOne_le_KO

theorem conj_mem_KOne₁ {w g : GL n k} (hw : w ∈ KO k n) (hg : g ∈ KOne k n) : w⁻¹ * g * w ∈ KOne k n := by
  refine mem_KOne.2 ?_
  have : (w⁻¹ * g * w).val - 1 = (w⁻¹).val * (g.val - 1) * w.val := by
    simp [mul_sub, sub_mul]
  rw [this]
  exact ((mem_KO.1 hw).2.mul_maxM (mem_KOne.1 hg)).mul_intM (mem_KO.1 hw).1

variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]

theorem leviEmb_mem_KOne₁ (e : (Σ a, m a) ≃ n) {g : Levi k m} (hg : ∀ a, g a ∈ KOne k (m a)) :
    leviEmb k e g ∈ KOne k n := by
  refine mem_KOne.2 fun i j => ?_
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  by_cases h : a = b
  · subst h
    have := mem_KOne.1 (hg a) i j
    simpa [Matrix.sub_apply, Matrix.one_apply] using this
  · have h' : e ⟨a, i⟩ ≠ e ⟨b, j⟩ := fun h' => h (congrArg Sigma.fst (e.injective h'))
    simp [Matrix.sub_apply, leviEmb_apply_ne k e g h, Matrix.one_apply_ne h']

theorem deltaHalf_eq_one {g : Levi k m} (hg : ∀ a, g a ∈ KOne k (m a)) : deltaHalf k m g = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => tame_det_of_mem_KOne (fun x hx => isUnram_absPow k _ x ?_) (hg a)
  simpa using Valuation.map_one_add_of_lt _ hx

theorem exists_fixed_of_parInd (e : (Σ a, m a) ≃ n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k m) W) {f : IndSp e ρ} (hf : f ∈ fixed (parInd e ρ) (KOne k n)) (h0 : f ≠ 0) :
    ∃ w : W, w ≠ 0 ∧ ∀ g : Levi k m, (∀ a, g a ∈ KOne k (m a)) → ρ g w = w := by
  obtain ⟨x, hx⟩ : ∃ x, f.1.1 x ≠ 0 := by
    by_contra! h
    exact h0 (Subtype.ext (Subtype.ext (funext h)))
  obtain ⟨p, c, hc, rfl⟩ := MultiIrr.exists_parab_mul e x
  refine ⟨f.1.1 c, fun h => hx (by rw [parInd_law, h]; simp), fun g hg => ?_⟩
  have h1 := parInd_law e ρ f ⟨_, leviEmb_mem_parab k e g⟩ c
  rw [leviProj_leviEmb, deltaHalf_eq_one hg, Units.val_one, one_smul] at h1
  have h2 := hf ⟨_, conj_mem_KOne₁ hc (leviEmb_mem_KOne₁ e hg)⟩
  have h3 := congrArg (fun F : IndSp e ρ => F.1.1 c) h2
  simp only [parInd_apply, MonoidHom.one_apply, Units.val_one, one_smul] at h3
  rw [← h1, ← h3]
  group

theorem fixed_of_isSubquotient (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL n k) V} (h : IsSubquotient π (multiProd e σ))
    (hv : ∃ v ∈ fixed π (KOne k n), v ≠ 0) (a : α) : ∃ v ∈ fixed (σ a) (KOne k (m a)), v ≠ 0 := by
  obtain ⟨S, F, hF⟩ := h
  obtain ⟨v, hv, hv0⟩ := hv
  obtain ⟨u, rfl⟩ := hF v
  have hS : IsSmooth S.toRepresentation := fun y => by
    have := isSmooth_parInd e (piTensor σ) y.1
    convert this using 3 with g
    exact Subtype.ext_iff
  obtain ⟨y, hy, hyu⟩ := IwahoriOnto.exists_fixed_map_eq hS isCompact_KOne₁ F.toLinearMap u fun g hg => by
    have h1 := hv ⟨g, hg⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1
    exact (F.isIntertwining _ _ g u).trans h1
  have hy0 : y.1 ≠ 0 := fun h => hv0 (by
    have : y = 0 := Subtype.ext h
    rw [this, map_zero] at hyu
    exact hyu.symm)
  obtain ⟨w, hw0, hw⟩ := exists_fixed_of_parInd e (piTensor σ) (f := y.1)
    (fun g => congrArg Subtype.val (hy g)) hy0
  obtain ⟨φ, hφ⟩ := exists_contract_ne_zero hw0 a
  refine ⟨_, fun g => ?_, hφ⟩
  rw [← contract_piTensor, hw _ fun b => ?_]
  · simp
  · by_cases hb : b = a
    · subst hb; simp
    · rw [Pi.mulSingle_eq_of_ne hb]; exact one_mem _

end GlobalTheory.SmGL.DepthZero

namespace GlobalTheory.SmGL

open GlobalTheory.PRep GlobalTheory.SplitRead

theorem depthZeroSupport : GlobalTheory.Published.DepthZeroSupport := by
  intro k _ _ _ _ n π s d σ h hv a
  obtain ⟨-, -, e, he⟩ := h
  exact DepthZero.fixed_of_isSubquotient e (fun a => (σ a).π) he hv a

end GlobalTheory.SmGL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsJLeviMulJPlus
section
noncomputable section

open GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace GlobalTheory.LocGL.IwahoriFactor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [Fintype n] in
theorem one_same (e : (Σ a, m a) ≃ n) (a : α) (i j : m a) :
    (1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) k) i j := by
  simp [Matrix.one_apply]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] in
theorem one_ne (e : (Σ a, m a) ≃ n) {a b : α} (h : a ≠ b) (i : m a) (j : m b) :
    (1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 :=
  Matrix.one_apply_ne fun e' => h (congrArg Sigma.fst (e.injective e'))

theorem exists_jPlus_mul_KOne (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ u ∈ jPlus k e, ∃ x ∈ KOne k n, g = u * x := by
  obtain ⟨h1, h3⟩ := mem_proRad.1 hg
  obtain ⟨h1, h2⟩ := mem_parahoric.1 h1
  let U : Matrix n n k := Matrix.of fun i j => if blk e i < blk e j then g.val i j else (1 : Matrix n n k) i j
  have hU : StepData.MaxM (U - g.val) := by
    intro i j
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    simp only [U, Matrix.sub_apply, Matrix.of_apply, blk_apply]
    rcases lt_trichotomy a b with h | rfl | h
    · simp [h]
    · rw [if_neg (lt_irrefl a), one_same, Valuation.map_sub_swap]
      exact h3 a i j
    · rw [if_neg h.not_gt, one_ne e h.ne', zero_sub, Valuation.map_neg]
      exact h2 a b i j h
  obtain ⟨x, hx, hgx⟩ := StepData.exists_mul_KOne h1 hU
  refine ⟨g * x, ⟨mem_unipRad.2 ⟨mem_parab_iff.2 fun a b i j h => ?_, fun a i j => ?_⟩,
    mul_mem h1 (StepData.KOne_le_KO hx)⟩, x⁻¹, inv_mem hx, by simp⟩
  · rw [hgx]
    simp only [U, Matrix.of_apply, blk_apply]
    rw [if_neg h.not_gt, one_ne e h.ne']
  · rw [hgx]
    simp only [U, Matrix.of_apply, blk_apply]
    rw [if_neg (lt_irrefl a), one_same]

theorem exists_KOne_mul_jPlus (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ x ∈ KOne k n, ∃ u ∈ jPlus k e, g = x * u := by
  obtain ⟨u, hu, x, hx, rfl⟩ := exists_jPlus_mul_KOne e hg
  exact ⟨u * x * u⁻¹, (Subgroup.mem_normalizer_iff.1 (KO_le_normalizer hu.2) x).1 hx, u, hu, by simp⟩

theorem proRad_eq_sup (e : (Σ a, m a) ≃ n) : proRad k e = KOne k n ⊔ jPlus k e := by
  refine le_antisymm (fun g hg => ?_) (sup_le (KOne_le_proRad e) (jPlus_le_proRad e))
  obtain ⟨x, hx, u, hu, rfl⟩ := exists_KOne_mul_jPlus e hg
  exact Subgroup.mul_mem_sup hx hu

theorem exists_mul_mem_parab (e : (Σ a, m a) ≃ n) {x : GL n k} (hx : x ∈ KOne k n) :
    ∃ c ∈ jMinus k e, x * c ∈ parab k e := by
  have hx' := StepData.mem_KOne.1 hx
  have hA : ∀ a : α, ∃ y ∈ KOne k n, y.val =
      Matrix.of fun i l => if a < blk e i then x.val i l else (1 : Matrix n n k) i l := fun a =>
    StepData.exists_mem_KOne fun i l => by
      simp only [Matrix.sub_apply, Matrix.of_apply]
      split_ifs
      · exact hx' i l
      · simp
  choose y hy hyv using hA
  obtain ⟨c, hc, hcv⟩ := StepData.exists_mem_KOne (M := Matrix.of fun i j => (y (blk e j))⁻¹.val i j)
    fun i j => StepData.mem_KOne.1 (inv_mem (hy (blk e j))) i j
  have key : ∀ i j, ∑ l, (if blk e j < blk e i then x.val i l else (1 : Matrix n n k) i l) * c.val l j =
      (1 : Matrix n n k) i j := fun i j => by
    have := congrFun (congrFun (y (blk e j)).mul_inv i) j
    rw [Matrix.mul_apply, hyv] at this
    rw [hcv]
    exact this
  have h1 : ∀ i j, blk e i ≤ blk e j → c.val i j = (1 : Matrix n n k) i j := fun i j h => by
    have := key i j
    simp only [if_neg h.not_gt] at this
    rwa [← Matrix.mul_apply, Matrix.one_mul] at this
  refine ⟨c, ⟨(mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i j h => ?_, fun a i j => ?_⟩, hc⟩,
    mem_parab_iff.2 fun a b i j h => ?_⟩
  · rw [h1 _ _ (by simpa using h.le), one_ne e h.ne]
  · rw [h1 _ _ (by simp), one_same]
  · have := key (e ⟨a, i⟩) (e ⟨b, j⟩)
    simp only [blk_apply, if_pos h] at this
    rw [Units.val_mul, Matrix.mul_apply, this, one_ne e h.ne']

theorem exists_jLevi_mul_jPlus (e : (Σ a, m a) ≃ n) {p : GL n k} (hp : p ∈ parab k e) (h : p ∈ KOne k n) :
    ∃ d ∈ jLevi k e, ∃ u ∈ jPlus k e, p = d * u := by
  obtain ⟨u, hu, hpu⟩ := exists_levi_mul_unip k e ⟨p, hp⟩
  have hd : leviEmb k e (leviProj k e ⟨p, hp⟩) ∈ jLevi k e :=
    ⟨_, fun a _ => StepData.mem_KOne.2 fun i j => by
      have := StepData.mem_KOne.1 h (e ⟨a, i⟩) (e ⟨a, j⟩)
      rw [Matrix.sub_apply, one_same] at this
      exact this, rfl⟩
  refine ⟨_, hd, u, ⟨hu, ?_⟩, hpu⟩
  rw [(inv_mul_eq_iff_eq_mul.2 hpu).symm]
  exact StepData.KOne_le_KO (mul_mem (inv_mem (jLevi_le_KOne e hd)) h)

theorem conj_mem_jPlus (e : (Σ a, m a) ≃ n) {d u : GL n k} (hd : d ∈ jLevi k e) (hu : u ∈ jPlus k e) :
    d * u * d⁻¹ ∈ jPlus k e := by
  have h := StepData.KOne_le_KO (jLevi_le_KOne e hd)
  obtain ⟨g, -, rfl⟩ := hd
  exact ⟨(Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer k e g) u).1 hu.1,
    (KO k n).mul_mem ((KO k n).mul_mem h hu.2) ((KO k n).inv_mem h)⟩

theorem plus_levi_minus (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ u ∈ jPlus k e, ∃ d ∈ jLevi k e, ∃ c ∈ jMinus k e, g = u * d * c := by
  obtain ⟨u, hu, x, hx, rfl⟩ := exists_jPlus_mul_KOne e hg
  obtain ⟨c, hc, hp⟩ := exists_mul_mem_parab e hx
  obtain ⟨d, hd, v, hv, h⟩ := exists_jLevi_mul_jPlus e hp (mul_mem hx hc.2)
  refine ⟨_, mul_mem hu (conj_mem_jPlus e hd hv), d, hd, c⁻¹, inv_mem hc, ?_⟩
  rw [eq_mul_inv_of_mul_eq h]
  group

theorem levi_plus_minus (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ proRad k e) :
    ∃ d ∈ jLevi k e, ∃ u ∈ jPlus k e, ∃ c ∈ jMinus k e, g = d * u * c := by
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := plus_levi_minus e hg
  exact ⟨d, hd, _, conj_mem_jPlus e (inv_mem hd) hu, c, hc, by group⟩

end GlobalTheory.LocGL.IwahoriFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEqOfPowSmulComparisonMatrix
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BSP.Height
private theorem matrix_map_smul {R S : Type*} [CommRing R] [CommRing S] {d : ℕ} (F : R →+* S) (c : R)
    (M : Matrix (Fin d) (Fin d) R) : (c • M).map F = F c • M.map F := by
  ext i j; simp

private theorem frobenius_height_matrix_relation {R D : Type*} [CommRing R] [CommRing D] {d : ℕ} (t : R →+* D)
    (ht : Function.Injective t) (φ : R →+* R) (Φ : D →+* D) (hΦ : ∀ a, Φ (t a) = t (φ a)) (n k m : ℕ) (a b : R)
    (Af Ag x : Matrix (Fin d) (Fin d) R) (ε : Matrix (Fin d) (Fin d) D) (hx : x.map t = (n : D) ^ k • ε)
    (key : t b ^ m • (Af.map t * ε.map Φ) = t a ^ m • (ε * Ag.map t)) :
    b ^ m • (Af * x.map φ) = a ^ m • (x * Ag) := by
  have hxφ : (x.map φ).map t = (n : D) ^ k • ε.map Φ := by
    have h1 : (x.map φ).map t = (x.map t).map Φ := by
      ext i j; simp only [Matrix.map_apply]; exact (hΦ (x i j)).symm
    rw [h1, hx]; ext i j; simp
  apply Matrix.map_injective ht
  simp only [Matrix.map_mul, matrix_map_smul, map_pow]
  rw [hxφ, hx, Matrix.mul_smul, Matrix.smul_mul, smul_comm _ ((n : D) ^ k), smul_comm _ ((n : D) ^ k), key]

theorem phi_eq_of_rel_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ι : Type), TopBasis (BK.hf f) bk.J ι → ∀ (k : ℕ) (x : Matrix (Fin d) (Fin d) B.A) (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f X) bk.ρ₀)), ht.Rel (BK.hf f X) f g ε → x.map (toDisc l (BK.hf f X) bk.ρ₀) = ((l : ℕ) : Disc l (BK.hf f X) bk.ρ₀) ^ k • ε → BK.hf g bk.E ^ (ht.a + s.N) • (ht.A.map (BK.hf f) * x.map B.D.φ) = BK.hf f bk.E ^ (ht.a + s.N) • (x * ht.A.map (BK.hf g)) := by
  intro l _ K bk d ρ τ s ht hper B f g ι hb k x ε hrel hx
  obtain ⟨hinj, hE, -, -⟩ := GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk B.A (BK.hf f) ι hb
  have hφ : ‖toDisc l (BK.hf f X) bk.ρ₀ (B.D.φ (BK.hf f X))‖ ≤ bk.ρ₀ := (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f f).2
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Disc l (BK.hf f X) bk.ρ₀ →+* Disc l (BK.hf f X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) B.D.φ Φ :=
    ⟨_, isDiscMap_map B.D.φ hφ⟩
  exact frobenius_height_matrix_relation _ hinj B.D.φ Φ hΦ.ext l k _ _ _ _ _ x ε hx
    (GlobalTheory.T.comparisonMatrix_frobenius_disc l K bk d ρ τ s ht hper B f hE f g ε hrel Φ hΦ)

end GlobalTheory.BSP.Height
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fTSpanCardBoundStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h1fT_span_card_bound : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ T : LocLat ↥(GK K) ℚ_[l] LL O, IsDR (P.PD K) T.ρ → ∃ s : Finset (LatticeCohomology T.L), Submodule.span O (s : Set (LatticeCohomology T.L)) = latticeFiniteCohomology (P.PD K) T.L ∧ s.card + finrank LL ↥(H0V T.ρ) ≤ finrank LL (FiniteCohomology (P.PD K) T.ρ) + finrank LL T.V := by
  first | exact @GlobalTheory.H1fGeneratorsAlt.h1fT_generators | exact GlobalTheory.H1fGeneratorsAlt.h1fT_generators | (intros; apply GlobalTheory.H1fGeneratorsAlt.h1fT_generators <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableConjMulTranslatePathStatement
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_conj_mul_translate_path' : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (c : ℝ → G), Continuous c → ∀ {f' : G → ℂ}, MemL2Quotient Γ μ f' → Continuous f' → ∀ (H : L2 Γ μ) (t : ℝ), Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => starRingEnd ℂ (H q) * f' (sec Γ q * c s)) ((volume.restrict (Set.uIoc 0 t)).prod (quotMeasure Γ μ)) := by
  first | exact @GlobalTheory.integrable_conj_mul_translate_path | exact GlobalTheory.integrable_conj_mul_translate_path | (intros; apply GlobalTheory.integrable_conj_mul_translate_path <;> assumption)
end

