module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.Bundle0001
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0176
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.JoinForms
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamJsymRead
section
open Formalism.L2.Col

noncomputable section

namespace GlobalTheory.LamRead

theorem sum_skip {F : Type} [Field F] {n r k : ℕ} (hr : r ≤ n) (hk : k ≤ r) (N : Matrix (Fin n) (Fin n) F) (f : ℕ → ℕ → F)
    (hf : ∀ i j : Fin n, f i.1 j.1 = N i j) :
    (∑ x : Fin n, ∑ y : Fin n, if (x : ℕ) + 1 = y ∧ (y : ℕ) < r ∧ (y : ℕ) ≠ k then N x y else 0) =
      ∑ i ∈ Finset.range (k - 1), f i (i + 1) + ∑ i ∈ Finset.range (r - k - 1), f (k + i) (k + i + 1) := by
  rw [Formalism.L2.G.sum_sup hr k ((Finset.range r).filter (fun x => x + 1 ≠ k))
    (fun x hx => by simp only [Finset.mem_filter, Finset.mem_range]; constructor <;> intro h <;> first | exact h.2 | exact ⟨by omega, h⟩) N,
    Finset.filter_filter, Finset.sum_filter]
  have h1 : ∀ x ∈ Finset.range r, (if x + 1 ≠ k ∧ x + 1 < r then Formalism.L2.G.entN N x (x + 1) else 0) =
      if x + 1 < r ∧ x + 1 ≠ k then f x (x + 1) else 0 := fun x hx => by
    by_cases hx' : x + 1 < r ∧ x + 1 ≠ k
    · rw [if_pos hx', if_pos ⟨hx'.2, hx'.1⟩]
      have a1 : x < n := by omega
      have a2 : x + 1 < n := by omega
      unfold Formalism.L2.G.entN
      rw [dif_pos ⟨a1, a2⟩]
      exact (hf ⟨x, a1⟩ ⟨x + 1, a2⟩).symm
    · rw [if_neg hx', if_neg (fun h => hx' ⟨h.2, h.1⟩)]
  rw [Finset.sum_congr rfl h1]
  obtain ⟨d, rfl⟩ : ∃ d, r = k + d := ⟨r - k, by omega⟩
  rw [Finset.sum_range_add, Nat.add_sub_cancel_left]
  by_cases hd : d = 0
  · subst hd
    rw [GlobalTheory.TopLawSym.sum_pred k _ _ fun p hp => by omega]
    simp
  · rw [GlobalTheory.TopLawSym.sum_pred k _ _ fun p hp => by omega,
      GlobalTheory.TopLawSym.sum_pred d (fun p => f (k + p) (k + p + 1)) (fun p => k + p + 1 < k + d ∧ k + p + 1 ≠ k) fun p hp => by omega]

theorem coarse_iff {r m t s i : ℕ} (ht : 0 < t) (hs : s < m) :
    coarse r (List.replicate m t) i = s + 1 ↔ r + s * t ≤ i ∧ i < r + s * t + t := by
  have hb := GlobalTheory.DatumLaw.blk_le (r := r) (a := r + m * t) hs le_rfl
  by_cases hir : i < r
  · rw [coarse_of_lt hir]
    omega
  · by_cases h2 : i < r + m * t
    · rw [GlobalTheory.TopLawSym.coarse_eq ht (by omega) h2, Nat.add_right_cancel_iff, Nat.div_eq_iff ht]
      omega
    · rw [coarse_of_le (by omega), blkIdx_replicate_of_le t m _ (by
        have := Nat.sub_le_sub_right (Nat.not_lt.1 h2) r
        rwa [Nat.add_sub_cancel_left] at this)]
      omega

theorem lamJsym_read (κ κ' K : Type) [CommRing κ] [Field κ'] [Field K] (e : κ →+* κ') (emb : K →+* ℂ) (ψ : AddChar κ K)
    (χ : ℕ → κˣ →* Kˣ) (ψ' : AddChar κ' ℂ) (χ' : ℕ → MulChar κ' ℂ) (n k r t m rS : ℕ) (h : r ≤ n) (hr : r = k + 2 * rS + 1)
    (ht : 0 < t) (hn : r + m * t ≤ n) (hψ : ∀ x, ψ' (e x) = emb (ψ x))
    (hχ : ∀ s, s < m → ∀ c : κˣ, χ' s (e c) = emb ((χ s c : Kˣ) : K)) (M : HJsym κ n k r t m rS h) :
    emb ((lamJsym ψ χ n k r t m rS h M : Kˣ) : K) =
      Formalism.L2.Forms.lamSym ψ' χ' k rS t m ((M.1 : Matrix (Fin n) (Fin n) κ).map e) := by
  let A : ℕ → ℕ → κ := fun i j => if h' : i < n ∧ j < n then (M.1 : Matrix (Fin n) (Fin n) κ) ⟨i, h'.1⟩ ⟨j, h'.2⟩ else 0
  have hA : ∀ i j : Fin n, A i.1 j.1 = (M.1 : Matrix (Fin n) (Fin n) κ) i j := fun i j => dif_pos ⟨i.2, j.2⟩
  have h0 : ((lamJsym ψ χ n k r t m rS h M : Kˣ) : K) =
      ((chiSymF ψ r k rS (HPar0 h _ _ M) : Kˣ) : K) *
        ((detChar χ n r (List.replicate m t) ⟨M.1, HPar_le h _ _ M.2⟩ : Kˣ) : K) := rfl
  have hrS : Formalism.L2.Forms.rSym k rS = r := hr.symm
  rw [h0, GlobalTheory.TopLawSym.chiSymF_val ψ (by omega) (HPar0 h _ _ M) A fun i j => hA (Fin.castLE h i) (Fin.castLE h j), detChar_apply,
    List.length_replicate, Units.coe_prod, map_mul, map_prod, ← hψ]
  unfold Formalism.L2.Forms.lamSym Formalism.L2.Forms.lamJ
  rw [hrS]
  congr 1
  · congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sum_skip h (by omega) _ (fun i j => e (A i j)) fun i j => by rw [hA]; rfl, map_add (f := _), map_sum, map_sum]
  · refine Finset.prod_congr rfl fun s hs => ?_
    rw [Finset.mem_range] at hs
    rw [← hχ s hs, GlobalTheory.TopLaw.blkDet_eq_dB (coarse r (List.replicate m t)) (s + 1) (r + s * t) t (GlobalTheory.DatumLaw.blk_le hs hn)
      (fun i _ => coarse_iff ht hs) ⟨M.1, HPar_le h _ _ M.2⟩ A hA]
    unfold GlobalTheory.DatumLaw.dB
    rw [RingHom.map_det]
    congr 2
    ext u v
    have hb := GlobalTheory.DatumLaw.blk_le hs hn
    have a1 : r + s * t + u.1 < n := by have := u.2; omega
    have a2 : r + s * t + v.1 < n := by have := v.2; omega
    show e (A (r + s * t + u.1) (r + s * t + v.1)) = Formalism.L2.Forms.entN _ (r + s * t + u.1) (r + s * t + v.1)
    unfold Formalism.L2.Forms.entN
    rw [dif_pos ⟨a1, a2⟩]
    exact congrArg e (hA ⟨_, a1⟩ ⟨_, a2⟩)

end GlobalTheory.LamRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalChartLastStepClasses
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.TC
open scoped TensorProduct

section Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem reL_refl {a : ℕ} (L : Submodule (𝓞 E) (Fin a → E)) : reL (rfl : a = a) L = L := by
  ext x
  simp only [reL, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem reGL_refl {a : ℕ} (R : Type) [CommRing R] (g : GL (Fin a) R) : reGL (rfl : a = a) R g = g := by
  ext i j
  simp [reGL]

theorem fvTie_of_coords (hc : CMData F E) (S : HSpace E) {cls : Type}
    (y : cls → Formalism.L2.Herm.UAf hc S) (lat : cls → Submodule (𝓞 E) S.V)
    (w : HeightOneSpectrum (𝓞 F)) (k : Type) [AddCommGroup k]
    (fz : ∀ c, Formalism.HermitianLatticesTheory.dual S.hT (lat c) → k)
    (Lb : Submodule (𝓞 E) (Fin S.rank → E)) {b : ℕ} (h : S.rank = b)
    (J : Matrix (Fin b) (Fin b) E) (hJ : J = S.gram.reindex (finCongr h) (finCongr h))
    (Lb' : Submodule (𝓞 E) (Fin b → E)) (hL : Lb' = reL h Lb)
    (y' : cls → GL (Fin b) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ c, y' c = reGL h _ (y c).1)
    (fT : latS (F := F) (w.adicCompletion F) (intV E w)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J Lb')) →+ k)
    (hfv : ∀ c (z : Formalism.HermitianLatticesTheory.dual S.hT (lat c))
      (hz : ((bc (prV (E := E) w) (y' c))⁻¹).1 *ᵥ
          (fun a => inclE (F := F) (w.adicCompletion F) (reV h E (Formalism.L2.Herm.crd S z.1) a)) ∈
        latS (F := F) (w.adicCompletion F) (intV E w)
          (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J Lb'))),
      fz c z = fT ⟨_, hz⟩) :
    Nonempty (Formalism.L2.Herm.FvTie hc S Lb y lat w k fz) := by
  subst h
  obtain rfl : J = S.gram := by rw [hJ]; ext i j; simp
  obtain rfl : Lb' = Lb := hL.trans (reL_refl Lb)
  obtain rfl : y' = fun c => (y c).1 := funext fun c => (hy c).trans (reGL_refl _ _)
  refine ⟨⟨fT, fun c z t ht => ?_⟩⟩
  have ht' : ((bc (prV (E := E) w) (y c).1)⁻¹).1 *ᵥ
      (fun a => inclE (F := F) (w.adicCompletion F) (reV (rfl : S.rank = S.rank) E (Formalism.L2.Herm.crd S z.1) a)) = t.1 := by
    have e : (fun a => inclE (F := F) (w.adicCompletion F) (reV (rfl : S.rank = S.rank) E (Formalism.L2.Herm.crd S z.1) a)) =
        fun a => inclE (F := F) (w.adicCompletion F) (Formalism.L2.Herm.crd S z.1 a) := rfl
    rw [e, ← ht, Matrix.mulVec_mulVec]
    simp
  have hz : ((bc (prV (E := E) w) (y c).1)⁻¹).1 *ᵥ
      (fun a => inclE (F := F) (w.adicCompletion F) (reV (rfl : S.rank = S.rank) E (Formalism.L2.Herm.crd S z.1) a)) ∈
      latS (F := F) (w.adicCompletion F) (intV E w)
        (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) S.gram Lb')) := by
    rw [ht']; exact t.2
  rw [hfv c z hz]
  exact congrArg fT (Subtype.ext ht')

theorem hform_reindex {a b : ℕ} (h : a = b) (σ : E →+* E) (G : Matrix (Fin a) (Fin a) E) (x y : Fin a → E) :
    hform σ (G.reindex (finCongr h) (finCongr h)) (reV h E x) (reV h E y) = hform σ G x y := by
  subst h
  have e : (G.reindex (finCongr (rfl : a = a)) (finCongr (rfl : a = a))) = G := by ext i j; simp
  rw [e]; rfl

end Generic

theorem crdN_mem_Ld {D : D7} (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i)
    (z : Formalism.L2.Herm.Ld D u i c) : crdN D i hi z.1 ∈ Ld D u i hi c := by
  refine Submodule.subset_span ?_
  intro x hx
  obtain ⟨x0, hx0, rfl⟩ := hx
  have h1 : (D.sp.X i).hT x0 z.1 ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    have := z.2
    simp only [Formalism.L2.Herm.Ld, Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf] at this
    exact this x0 hx0
  rw [Formalism.L2.Herm.hT_crd D.sp.cm] at h1
  have h2 := hform_reindex (rankN D i hi) (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X i).gram
    (Formalism.L2.Herm.crd _ x0) (Formalism.L2.Herm.crd _ z.1)
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 h1
  exact ⟨r, hr.trans h2.symm⟩


set_option maxHeartbeats 4000000 in
theorem fvTie_top {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u))
    (A : ∀ u, Formalism.L2.Herm.AtT D u (H.vT u) (H.Fv u)) (hH : CarH H F) (hT : CarT H F A) (u : D.what₂.Word)
    (h1 : 1 ≤ D.R.m) (v : (D.mem u).A.vT) (β : H.Ch u D.R.m) :
    Nonempty (Formalism.L2.Herm.FvTie D.sp.cm (D.sp.X D.R.m) (H.lev u D.R.m h1 le_rfl β).Lb (H.cls u D.R.m h1 le_rfl β).y
      (fun c => D.clsLat u D.R.m c.1) (H.vT u v).1 ((D.mem u).A.Fv v)
      (fun c z => (D.fm u).fv D.R.m v c.1 ((A u).pr D.R.m v c.1 z))) := by
  obtain rfl : β = chM H u := @Subsingleton.elim _ (@Unique.instSubsingleton _ (H.Ch_m u).some) _ _
  have key : ∀ w, w = ((F u).atT.eV v).1 →
      Nonempty (Formalism.L2.Herm.FvTie D.sp.cm (D.sp.X D.R.m) (H.lev u D.R.m h1 le_rfl (chM H u)).Lb
        (H.cls u D.R.m h1 le_rfl (chM H u)).y (fun c => D.clsLat u D.R.m c.1) w ((D.mem u).A.Fv v)
        (fun c z => (D.fm u).fv D.R.m v c.1 ((A u).pr D.R.m v c.1 z))) := by
    intro w hw
    subst hw
    have hc := hH.carM u
    refine fvTie_of_coords D.sp.cm (D.sp.X D.R.m) _ _ _ _ _ _ (rankN D D.R.m le_rfl) (gramN D D.R.m le_rfl) rfl
      ((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.Lb hc.Lb_eq
      (fun c => (((F u).cls D.R.m le_rfl (Or.inr rfl)).y c.1).1) (fun c => hc.y_eq c.1)
      (((F u).fMe D.R.m le_rfl (Or.inr rfl) v).toAddMonoidHom.comp
        (((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.fT _ ((F u).atT.eV v).2).toAddMonoidHom) ?_
    intro c z hz
    have hz' := crdN_mem_Ld u D.R.m le_rfl c.1 z
    have e1 := (F u).fv D.R.m le_rfl (Or.inr rfl) v c.1 ⟨_, hz'⟩ hz
    have e2 := hT.pr u D.R.m le_rfl v c.1 z ⟨_, hz'⟩ rfl
    exact (congrArg (fun p => (D.fm u).fv D.R.m v c.1 p) e2.symm).trans e1
  exact key _ (by rw [hH.eV u])


set_option maxHeartbeats 4000000 in
theorem fvTie_chart_top : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (h1 : 1 ≤ (I.rec7 l Z).R.m) (v : ((I.rec7 l Z).mem u).A.vT) (β : H.Ch u (I.rec7 l Z).R.m), Nonempty (Formalism.L2.Herm.FvTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) (H.lev u (I.rec7 l Z).R.m h1 le_rfl β).Lb (H.cls u (I.rec7 l Z).R.m h1 le_rfl β).y (fun c => (I.rec7 l Z).clsLat u (I.rec7 l Z).R.m c.1) (H.vT u v).1 (((I.rec7 l Z).mem u).A.Fv v) (fun c z => ((I.rec7 l Z).fm u).fv (I.rec7 l Z).R.m v c.1 ((A u).pr (I.rec7 l Z).R.m v c.1 z))) := by
  intro B X I _ _ l Z H F A _ hH hT u h1 v β
  exact fvTie_top H F A hH hT u h1 v β

end GlobalTheory.Mem.Col2.TC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingWeilActionFiniteExtension
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocDec

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem exists_lifts_mul_mem (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (ι : Ω →ₐ[E] Kbar w) (θ : Dec (F := E) A ≃* GalLoc w) (hθ : Continuous θ)
    (hl : ∀ σ : Dec (F := E) A, Lifts ι (θ σ) (σ : G E Ω)) (g : GalLoc w) (H : Subgroup (GalLoc w))
    (hH : IsOpen (H : Set (GalLoc w))) :
    ∃ (σ : Weil h) (g' : GalLoc w), Lifts ι g' (σ : G E Ω) ∧ g⁻¹ * g' ∈ H := by
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  set d := θ.symm g with hd
  let S : Set (Dec (F := E) A) := (fun σ => g⁻¹ * θ σ) ⁻¹' (H : Set (GalLoc w))
  have hS : IsOpen S := hH.preimage (continuous_const.mul hθ)
  have hdS : d ∈ S := by
    show g⁻¹ * θ d ∈ H
    rw [hd, MulEquiv.apply_symm_apply, inv_mul_cancel]
    exact H.one_mem
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp hS
  have hdt : (d : G E Ω) ∈ t := by
    rw [← hts] at hdS
    exact hdS
  have hnhds : {x : G E Ω | (d : G E Ω) * x ∈ t} ∈ nhds (1 : G E Ω) := by
    apply (continuous_const_mul (d : G E Ω)).continuousAt.preimage_mem_nhds
    simpa using ht.mem_nhds hdt
  obtain ⟨F, hF, hFs⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp hnhds
  let pb := Field.powerBasisOfFiniteOfSeparable E F
  obtain ⟨τ, hτW, hτ⟩ := GlobalTheory.T.weilGroupAtPlace_dense_in_decompositionGroup E Ω A w h (d : G E Ω) d.2 (pb.gen : Ω)
  have hfix : (d : G E Ω)⁻¹ * τ ∈ F.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have e : (((d : G E Ω)⁻¹ * τ : G E Ω) : Ω →ₐ[E] Ω).comp F.val = F.val := pb.algHom_ext (by
      show ((d : G E Ω)⁻¹ * τ) (pb.gen : Ω) = pb.gen
      rw [AlgEquiv.mul_apply, hτ]
      show ((d : G E Ω)⁻¹ * (d : G E Ω)) (pb.gen : Ω) = pb.gen
      simp)
    exact congrArg (fun φ : F →ₐ[E] Ω => φ ⟨x, hx⟩) e
  have hτt : τ ∈ t := by
    have := hFs hfix
    simpa using this
  let σ : Dec (F := E) A := ⟨τ, Weil_le_Dec h hτW⟩
  have hσS : σ ∈ S := by
    rw [← hts]
    exact hτt
  exact ⟨⟨τ, hτW⟩, θ σ, hl σ, hσS⟩

end GlobalTheory.LocDec

namespace GlobalTheory.LocDec

theorem eq_adjoin_of_fixing_iff (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [Algebra E K] [IsScalarTower E K Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w)
    (hι : IsLocEmb A w ι) (L : IntermediateField (w.adicCompletion E) (Kbar w))
    [FiniteDimensional (w.adicCompletion E) L]
    (hfix : ∀ (σ : Weil h) (g : GalLoc w), Lifts ι g σ →
      ((∀ z ∈ L, g z = z) ↔ ∀ x : K, (σ : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x)) :
    L = IntermediateField.adjoin (w.adicCompletion E) (Set.range fun x : K => ι (algebraMap K Ω x)) := by
  obtain ⟨θ, hθ, -, hl⟩ := decomposition_mulEquiv_galLoc E Ω A w h ι hι
  set Kw := w.adicCompletion E
  have : CharZero Kw := charZero_of_injective_algebraMap (algebraMap E Kw).injective
  have : IsGalois Kw (Kbar w) := IsAlgClosure.isGalois Kw (Kbar w)
  set M := IntermediateField.adjoin Kw (Set.range fun x : K => ι (algebraMap K Ω x)) with hM
  have hfx : ∀ (σ : G E Ω) (g' : GalLoc w), Lifts ι g' σ → ∀ x : K,
      (g' (ι (algebraMap K Ω x)) = ι (algebraMap K Ω x) ↔ σ (algebraMap K Ω x) = algebraMap K Ω x) :=
    fun σ g' hg x => by rw [hg]; exact ι.toRingHom.injective.eq_iff
  have : FiniteDimensional E K := Module.Finite.of_restrictScalars_finite ℚ E K
  let pb := Field.powerBasisOfFiniteOfSeparable E K
  have hprim : ∀ σ : G E Ω, σ (algebraMap K Ω pb.gen) = algebraMap K Ω pb.gen →
      ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω x := by
    intro σ hσ x
    have e : ((σ : Ω →ₐ[E] Ω).comp (IsScalarTower.toAlgHom E K Ω)) = IsScalarTower.toAlgHom E K Ω :=
      pb.algHom_ext (by simpa using hσ)
    simpa using congrArg (fun φ : K →ₐ[E] Ω => φ x) e
  have hopen : ∀ z : Kbar w,
      IsOpen ((IntermediateField.adjoin Kw {z}).fixingSubgroup : Set (GalLoc w)) := fun z => by
    have : FiniteDimensional Kw (IntermediateField.adjoin Kw {z}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
    exact IntermediateField.fixingSubgroup_isOpen _
  have hmemz : ∀ (z : Kbar w) (k : GalLoc w), k ∈ (IntermediateField.adjoin Kw {z}).fixingSubgroup → k z = z :=
    fun z k hk => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk z (IntermediateField.mem_adjoin_simple_self _ _)
  have hLopen : IsOpen (L.fixingSubgroup : Set (GalLoc w)) := IntermediateField.fixingSubgroup_isOpen L
  have hLfix : ∀ k : GalLoc w, k ∈ L.fixingSubgroup → ∀ z ∈ L, k z = z :=
    fun k hk => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk
  apply le_antisymm
  · intro z hz
    rw [← InfiniteGalois.fixedField_fixingSubgroup M, IntermediateField.mem_fixedField_iff]
    intro g hg
    have hga : g (ι (algebraMap K Ω pb.gen)) = ι (algebraMap K Ω pb.gen) :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _
        (IntermediateField.subset_adjoin _ _ ⟨pb.gen, rfl⟩)
    obtain ⟨σ, g', hlift, hk⟩ := exists_lifts_mul_mem A w h ι θ hθ hl g
      (L.fixingSubgroup ⊓ (IntermediateField.adjoin Kw {ι (algebraMap K Ω pb.gen)}).fixingSubgroup)
      (hLopen.inter (hopen _))
    have hg' : g' = g * (g⁻¹ * g') := by group
    have h1 : g' (ι (algebraMap K Ω pb.gen)) = ι (algebraMap K Ω pb.gen) := by
      rw [hg', AlgEquiv.mul_apply, hmemz _ _ (Subgroup.mem_inf.1 hk).2, hga]
    have h2 := hprim σ ((hfx σ g' hlift pb.gen).1 h1)
    have h3 := (hfix σ g' hlift).2 h2 z hz
    rw [hg', AlgEquiv.mul_apply, hLfix _ (Subgroup.mem_inf.1 hk).1 z hz] at h3
    exact h3
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    rw [← InfiniteGalois.fixedField_fixingSubgroup L]
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro g hg
    obtain ⟨σ, g', hlift, hk⟩ := exists_lifts_mul_mem A w h ι θ hθ hl g
      (L.fixingSubgroup ⊓ (IntermediateField.adjoin Kw {ι (algebraMap K Ω x)}).fixingSubgroup)
      (hLopen.inter (hopen _))
    have hg' : g' = g * (g⁻¹ * g') := by group
    have h1 : ∀ z ∈ L, g' z = z := fun z hz => by
      rw [hg', AlgEquiv.mul_apply, hLfix _ (Subgroup.mem_inf.1 hk).1 z hz, hLfix g hg z hz]
    have h2 := (hfx σ g' hlift x).2 ((hfix σ g' hlift).1 h1 x)
    rw [hg', AlgEquiv.mul_apply, hmemz _ _ (Subgroup.mem_inf.1 hk).2] at h2
    exact h2

theorem eq_adjoin_of_fixing_iff_weil : ∀ (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra E K] [IsScalarTower E K Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∀ L : IntermediateField (w.adicCompletion E) (Kbar w), FiniteDimensional (w.adicCompletion E) L → (∀ (σ : Weil h) (g : GalLoc w), Lifts ι g σ → ((∀ z ∈ L, g z = z) ↔ ∀ x : K, (σ : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x)) → L = IntermediateField.adjoin (w.adicCompletion E) (Set.range fun x : K => ι (algebraMap K Ω x)) := by
  intro E K Ω _ _ _ _ _ _ _ _ _ _ _ A w h ι hι L _ hfix
  exact eq_adjoin_of_fixing_iff E K Ω A w h ι hι L hfix

end GlobalTheory.LocDec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeSmoothModelsOnThetaTargets
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowSmooth

open GlobalTheory.ConjDS GlobalTheory.ConjExt Formalism.MainNotions.S

variable {D : D7} {V : HSp D}

def glue {S : D.what₂.Tau → D.what₂.Tau → SPar} (N : ∀ τ, DSModel V (S τ)) : DSModel V fun τ => S τ τ where
  H τ := (N τ).H τ
  σ τ := (N τ).σ τ
  lam τ := (N τ).lam τ
  ε τ := (N τ).ε τ
  fr τ := (N τ).fr τ
  enum τ := (N τ).enum τ
  ds τ := (N τ).ds τ
  fr_unit τ := (N τ).fr_unit τ
  fr_gram τ := (N τ).fr_gram τ

theorem dualPar_dualPar (S : SPar) : dualPar (dualPar S) = S := by
  unfold dualPar
  ext x
  simp only [Finset.mem_image]
  exact ⟨fun ⟨_, ⟨y, hy, e⟩, e'⟩ => by subst e e'; simpa using hy,
    fun hx => ⟨(-x.1, x.2), ⟨x, hx, rfl⟩, by simp⟩⟩

theorem low_of_conj {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (h : lowKSub ((conjModel M).ε τ) ((conjModel M).lam τ) ((conjModel M).σ τ) ≤ (conjModel M).sm τ) :
    lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ≤ M.sm τ := by
  intro w hw
  let c : (conjModel M).H τ ≃ₗᵢ⋆[ℂ] M.H τ := cj (M.H τ)
  have h1 := h (lowKSub_transfer (ε := M.ε τ) (ε' := (conjModel M).ε τ) (σ' := (conjModel M).σ τ) (fun _ => rfl) c
    (fun _ _ => rfl) hw)
  have h2 : ∀ y ∈ (conjModel M).sm τ, c y ∈ M.sm τ := fun y hy => by
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (smoothVec_map c (conj_rep M τ) hy)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [LinearIsometryEquiv.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  have h3 := h2 _ h1
  simpa using h3

theorem shape_at {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (h : HCParam D.R) {p q : ℕ}
    (hn : V.rank = D.R.r) (hpq : p + q = V.rank)
    (hS : S τ = Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW h p q)) :
    Formalism.QuantumDeterminants.IsHCParam (M.lam τ) ∧ ∃ p ≤ V.rank, ∀ a, M.ε τ a = decide ((a : ℕ) < p) := by
  have key := GlobalTheory.HolDict.isEnum_holPar_kapW h hn hpq (hS ▸ M.enum τ)
  refine ⟨⟨(M.enum τ).1, fun a => ?_⟩, p, by omega, fun a => (key a).2⟩
  obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int h a
  obtain ⟨s, hs⟩ := Formalism.L2.NTheta.odd_r D.R
  refine ⟨z - s, ?_⟩
  have hr : ((V.rank : ℕ) : ℝ) = 2 * s + 1 := by rw [hn, hs]; push_cast; rfl
  rw [(key a).1, hz, hr]
  push_cast
  ring

theorem lowSm_MW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i σ, LowSm (R.MW i σ) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i σ
  have key : ∀ τ, ∃ (S : D.what₂.Tau → SPar) (N : DSModel (Wc D i) S),
      (Formalism.QuantumDeterminants.IsHCParam (N.lam τ) ∧ ∃ p ≤ (Wc D i).rank, ∀ a, N.ε τ a = decide ((a : ℕ) < p)) ∧
      (lowKSub (N.ε τ) (N.lam τ) (N.σ τ) ≤ N.sm τ →
        lowKSub ((R.MW i σ).ε τ) ((R.MW i σ).lam τ) ((R.MW i σ).σ τ) ≤ (R.MW i σ).sm τ) := fun τ => by
    have hpq := GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW (D := D) i τ
    by_cases hb : labE σ (lab σ τ) = tauE D τ
    · exact ⟨_, R.MW i σ, shape_at _ τ (D.hc (lab σ τ)) (rank_Wc i) hpq (if_pos hb), id⟩
    · refine ⟨_, conjModel (R.MW i σ), shape_at _ τ (D.hc (lab σ τ)) (rank_Wc i) hpq ?_, low_of_conj _ τ⟩
      unfold Links.parAt
      rw [if_neg hb, dualPar_dualPar]
      rfl
  choose S N hN hL using key
  exact fun τ => hL τ ((GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ (glue N) hN).1 τ)

end GlobalTheory.LowSmooth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyClassMapAboveLastStep
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

noncomputable def clDown {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ) (hi : B.R.m < i)
    (c : (I.stp u a i).Cl) : (I.stp u I.mu0 i).Cl :=
  (I.stp u I.mu0 i).cl (Idx.top I.sel (I.tup I.mu0) (I.idx I.mu0) (le_of_lt hi))
    ⟨(extTo (I.Q I.mu0) ((I.stp u a i).rep c).1.1, ∅), by
      rw [ysAt_ys_of_ne I.sel (I.tup I.mu0) (I.cst I.mu0) (by omega)]
      rfl⟩

theorem nonempty_clDown : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), B.R.m < i →
    Nonempty ((I.stp u a i).Cl → (I.stp u I.mu0 i).Cl) :=
  fun I _ u a i hi => ⟨I.clDown u a i hi⟩

end GlobalTheory.Mem.Col2.TC
end

