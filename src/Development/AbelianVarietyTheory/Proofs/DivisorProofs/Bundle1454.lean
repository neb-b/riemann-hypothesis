module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalUnitarySplitDenominator
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryAdelicDecompositionSplitSupport
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryCongruentLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixDetNotMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1415
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0909
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalUnitaryMoveSelfDualToSplit
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SplitMove

section General

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.UnRep.FullReps GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
open scoped TensorProduct Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conj_conj (v : Fin n → E) :
    (fun j => IsCMField.complexConj E (IsCMField.complexConj E (v j))) = v :=
  funext fun j => IsCMField.complexConj_apply_apply E (v j)

theorem unimod_conj (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {Λ : GenLat E n} (hU : Λ.Unimod) :
    (conjLat H Λ.La).Unimod := by
  have hr : ∀ x : E, x ∈ (algebraMap (𝓞 E) E).range → IsCMField.complexConj E x ∈ (algebraMap (𝓞 E) E).range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨H.bar a, H.bar_eq a⟩
  intro v
  rw [mem_conjLat, hU]
  constructor
  · intro hv w hw
    have := hr _ (hv _ hw)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_mul, IsCMField.complexConj_apply_apply] using this
  · intro hv w hw
    have := hr _ (hv (fun j => IsCMField.complexConj E (w j)) (by rw [mem_conjLat, conj_conj]; exact hw))
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_mul, IsCMField.complexConj_apply_apply] using this

theorem trivAt_conj (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {Λ : GenLat E n} {N : ℕ} (hT : Λ.TrivAt N) :
    (conjLat H Λ.La).TrivAt N := by
  obtain ⟨k, hk, h1, h2⟩ := hT
  exact ⟨k, hk, conjLat_le H (by rw [← H.bar_eq, map_natCast])
    ⟨(Move.span_smul_le _ _ _).1 h1, (Move.span_smul_le _ _ _).1 h2⟩⟩

theorem congAt_of_congAtA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    {N M : ℕ} (hM : 0 < M) {γ : Matrix (Fin n) (Fin n) E} (h : CongAtA F L N M (fm F γ)) :
    GlobalTheory.UnRep.CongAt L N M γ := by
  obtain ⟨t, ht, h⟩ := h
  have hrat := (hat_rational_points_and_approx F E n L hfg hsp).1
  refine ⟨t, ht, fun v hv => ?_⟩
  obtain ⟨w, hw, e⟩ := h _ ((hrat v).2 hv)
  have hME : (M : E) ≠ 0 := by exact_mod_cast hM.ne'
  have key : t • (γ *ᵥ v - v) = M • ((M : E)⁻¹ • (t • (γ *ᵥ v - v))) := by
    rw [← Nat.cast_smul_eq_nsmul E M, smul_smul, mul_inv_cancel₀ hME, one_smul]
  refine ⟨_, ?_, key⟩
  rw [← hrat]
  have e' : fv F ((M : E)⁻¹ • (t • (γ *ᵥ v - v))) = w := by
    refine Move.nsmul_cancel _ hM ?_
    rw [← cap_fv_nsmul, ← key, cap_fv_nsmul, Move.fv_sub, Move.fv_mulVec, e]
  rw [e']
  exact hw

theorem exists_move_matrix (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (N : ℕ) (hN : 0 < N) (Λ : GenLat E n)
    (hU : Λ.Unimod) (hT : Λ.TrivAt N) :
    ∃ (γ : Matrix (Fin n) (Fin n) E) (h : GL (Fin n) (RA (maximalRealSubfield E) E))
      (Lh : Submodule (𝓞 E) (Fin n → E)), IsUnitaryM γ ∧
      (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.CongAt N (fun i => γ i j) fun i => (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) ∧
      IsUnA (IsCMField.complexConj E) 1 h.1 ∧ SuppSplit (IsCMField.complexConj E) N h.1 ∧
      (Lh : Set (Fin n → E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield E) h.1 (stdLat E n) ∧
      actLat γ Λ = conjLat H Lh := by
  obtain ⟨hherm, hrk, hfg, hsp, -, -, -, hun⟩ := StdInhab.main E H n
  obtain ⟨g, hg, hΛ, hgc⟩ := GlobalTheory.AdelTranslate.exists_adelic_translate E H n N _ hN (unimod_conj H hU)
    (trivAt_conj H hT)
  obtain ⟨γ, h, k, hγ, hh, -, e, hs, hk, hk'⟩ := GlobalTheory.UnRep.exists_rep_suppSplit (maximalRealSubfield E) E
    (IsCMField.complexConj E) n 1 hherm hrk (stdLat E n) hfg hsp g N hg hN
  obtain ⟨Lh, hLh, -⟩ := GlobalTheory.AdLat.exists_lattice_latOf (maximalRealSubfield E) E n (stdLat E n) h hfg hsp
  have hu : adjM γ.1 * γ.1 = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply, ← (hun _).1 hγ i j]
    rfl
  have hu' : γ.1 * adjM γ.1 = 1 := mul_eq_one_comm.1 hu
  have hδ : adjM γ.1ᵀ * γ.1ᵀ = 1 := by
    rw [show adjM γ.1ᵀ = (adjM γ.1)ᵀ from rfl, ← Matrix.transpose_mul, hu', Matrix.transpose_one]
  have hδ' : γ.1ᵀ * adjM γ.1ᵀ = 1 := mul_eq_one_comm.1 hδ
  have ck : CongAtA (maximalRealSubfield E) (stdLat E n) N N (k⁻¹).1 := by
    refine ⟨1, Nat.coprime_one_left _, fun z hz => ?_⟩
    obtain ⟨w, hw, e⟩ := hk _ (hk' z hz)
    refine ⟨-w, neg_mem hw, ?_⟩
    rw [one_smul, smul_neg, ← e, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, neg_sub]
  have ch : CongAtA (maximalRealSubfield E) (stdLat E n) N N (h⁻¹).1 := by
    obtain ⟨ε, -, -, he, hcut⟩ := hs
    obtain ⟨t, ht, hb⟩ := (idempotent_adeles_small_matrices (maximalRealSubfield E) E n (stdLat E n) hfg hsp).2.2.2.1
      N N ε ((h⁻¹).1 - 1) hN fun v hv => by
        by_contra h0
        exact (he v h0).2 hv
    refine ⟨t, ht, fun z hz => ?_⟩
    obtain ⟨w, hw, e⟩ := hb z hz
    rw [cut_inv h _ hcut, Matrix.sub_mulVec, Matrix.one_mulVec] at e
    exact ⟨w, hw, e⟩
  have eγ : fm (maximalRealSubfield E) γ.1 = g.1 * (k⁻¹).1 * (h⁻¹).1 := by
    rw [e, Units.mul_inv_cancel_right, Units.mul_inv_cancel_right]
  have cγ : GlobalTheory.UnRep.CongAt (stdLat E n) N N γ.1 := by
    refine congAt_of_congAtA (F := maximalRealSubfield E) _ hfg hsp hN ?_
    rw [eγ]
    exact LatForm.congAtA_mul _ _ _ _ _ (LatForm.congAtA_mul _ _ _ _ _ (hgc N hN) ck) ch
  have hmove : ∀ u, u ∈ Lh ↔ γ.1 *ᵥ u ∈ (conjLat H Λ.La).La := by
    intro u
    rw [← SetLike.mem_coe, ← SetLike.mem_coe (p := (conjLat H Λ.La).La), hΛ, hLh]
    constructor
    · rintro ⟨z, hz, ez⟩
      refine ⟨_, hk' z hz, ?_⟩
      rw [Move.fv_mulVec, ← ez, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e, Units.mul_inv_cancel_right]
    · rintro ⟨z, hz, ez⟩
      refine ⟨k.1 *ᵥ z, ?_, ?_⟩
      · obtain ⟨w, hw, e⟩ := hk z hz
        rw [sub_eq_iff_eq_add.1 e]
        exact add_mem (nsmul_mem hw _) hz
      · have := congrArg (fun x => fm (maximalRealSubfield E) (γ⁻¹).1 *ᵥ x) ez
        rw [← Move.fv_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, e,
          ← mul_assoc, ← mul_assoc, ← FullReps.fm_mul, Units.inv_mul, FullReps.fm_one, one_mul] at this
        rw [Matrix.mulVec_mulVec, this]
  refine ⟨γ.1ᵀ, h, Lh, hδ, fun j => ?_, hh, hs, hLh, congrArg GenLat.mk (Submodule.ext fun v => ?_)⟩
  · obtain ⟨t, ht, hc⟩ := cγ
    refine ⟨t, ht, fun i => ?_⟩
    obtain ⟨w, hw, ew⟩ := hc _ (StdInhab.single_mem n i)
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hw j trivial)
    refine ⟨b, ?_⟩
    have := congrFun ew j
    rw [Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul, ← hb, Pi.sub_apply,
      Matrix.mulVec_single_one] at this
    refine Eq.trans ?_ this
    congr 2
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Pi.single_apply, Ne.symm hij]
  · have hc : (fun j => IsCMField.complexConj E ((γ.1 *ᵥ fun j => IsCMField.complexConj E (v j)) j)) =
        adjM γ.1ᵀ *ᵥ v := by
      funext j
      simp [Matrix.mulVec, dotProduct, adjM]
    change v ∈ (actLat γ.1ᵀ Λ).La ↔ v ∈ (conjLat H Lh).La
    rw [mem_conjLat, hmove, mem_conjLat, hc]
    constructor
    · rintro ⟨u, hu, rfl⟩
      change adjM γ.1ᵀ *ᵥ (γ.1ᵀ *ᵥ u) ∈ Λ.La
      rw [Matrix.mulVec_mulVec, hδ, Matrix.one_mulVec]
      exact hu
    · intro hv
      refine ⟨_, hv, ?_⟩
      change γ.1ᵀ *ᵥ (adjM γ.1ᵀ *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, hδ', Matrix.one_mulVec]

end General

open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_move_to_split : ∀ (D : D7) (V : HSp D), V.gram = 1 → Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (H : Geo.Tor.Host D.host.E) (N : ℕ), 0 < N → ∀ Λ : GenLat D.host.E V.rank, Λ.Unimod → Λ.TrivAt N → ∃ (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (h : GA D V), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.IsUnitaryM γ ∧ (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.CongAt N (fun i => γ i j) fun i => (((1 : Matrix (Fin V.rank) (Fin V.rank) (𝓞 D.host.E)) i j : 𝓞 D.host.E) : D.host.E)) ∧ h ∈ GfC V ∧ GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom V h).1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.actLat γ Λ = GlobalTheory.UnRep.FullReps.conjLat H (Bridge.hLat V (fin V h)) := by
  intro D V hg hL H N hN Λ hU hT
  obtain ⟨γ, h', Lh, h1, h2, h3, h4, h5, h6⟩ := exists_move_matrix H N hN Λ hU hT
  have hc : GlobalTheory.Member.cF D = IsCMField.complexConj D.host.E := AlgEquiv.ext fun _ => rfl
  obtain ⟨-, -, -, lift, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  obtain ⟨h, hh, eh⟩ := lift h' (by
    rw [show (HSpace.gram V)ᵀ = 1 by rw [hg, Matrix.transpose_one], hc]
    exact h3)
  refine ⟨γ, h, h1, h2, hh, ?_, ?_⟩
  · rw [eh, hc]; exact h4
  · rw [GlobalTheory.SplitReps.hLat_one] at hL
    rw [GlobalTheory.SplitReps.hLat_eq V (FWT.fin V h) Lh (by
      rw [hL]
      change _ = GlobalTheory.AdLat.latOf D.host.F (finHom V h).1 _
      rw [eh]
      exact h5)]
    exact h6

end GlobalTheory.SplitMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSphericalCuspFormWhittakerNeZero
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

noncomputable section

namespace GlobalTheory.JSW.NzSph

theorem finite_bad (E : Type) [Field E] [NumberField E] (a : ℕ) (k : GL (Fin a) (Af E)) :
    {w : HeightOneSpectrum (𝓞 E) | GeneralLinearGroup.map (pLoc E w) k ∉ KGL w (n := a)}.Finite :=
  GlobalTheory.T.finiteAdelicGL_mem_integral_cofinite_places E a k

theorem exists_outside (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (k : GL (Fin a) (Af E)) : ∃ k' : GL (Fin a) (Af E),
      (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k' = GeneralLinearGroup.map (pLoc E w) k) ∧
      ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k' = 1 :=
  _root_.GlobalTheory.outsideS_elt E a S k

theorem local_decomp (E : Type) [Field E] [NumberField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (g : GL (Fin a) (w.adicCompletion E)) :
    ∃ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a), ∃ (N : ℕ) (l : Fin a → ℕ), ∃ k ∈ KGL w (n := a),
      g = u * GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * k :=
  GlobalTheory.T.iwasawa_decomposition_adicCompletionGL_diagonalPowers E a w ϖ hϖ g

theorem act_fin_eq_of_outside (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a)
    (hφ : IsAutForm φ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) (k : GL (Fin a) (Af E))
    (hk : ∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k ∈ KGL w (n := a))
    (hk1 : ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k = 1) : act (.fin k) φ = φ :=
  GlobalTheory.T.smoothAutomorphicForm_fixed_of_locally_integral_fixed E a φ hφ S hS k hk hk1

end GlobalTheory.JSW.NzSph

namespace GlobalTheory.JSW.NzSph

open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.MultiplicityOne

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem map_pLoc_pFin (w : HeightOneSpectrum (𝓞 E)) (g : GA E a) :
    GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) =
      GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g := by
  ext; rfl

theorem comp_finGL (v : HeightOneSpectrum (𝓞 E)) (h : GL (Fin a) (Af E)) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E a h) = GeneralLinearGroup.map (pLoc E v) h := by
  rw [finGL, map_cornerGL_of_hom (sFin E) ((pLoc E v).comp (pFin E)) (pLoc E v) (fun x => rfl)]

theorem diagPow_const_comm {K : Type} [CommRing K] {n : ℕ} (c : Kˣ) (N : ℕ) (h : GL (Fin n) K) :
    GlobalTheory.JSW.diagPow c (fun _ : Fin n => N) * h = h * GlobalTheory.JSW.diagPow c (fun _ : Fin n => N) := by
  ext i j
  simp [GlobalTheory.JSW.diagPow, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

variable [_root_.NumberField.IsTotallyComplex E]

theorem whit_act_fin (φ : Sm E a) (k : GL (Fin a) (Af E)) (y : GA E a) :
    whit (act (.fin k) φ).1 y = whit φ.1 (y * finGL E a k) := by
  rw [whit_mul_right]; rfl

theorem act_fin_mul (k k' : GL (Fin a) (Af E)) (φ : Sm E a) :
    act (.fin (k * k')) φ = act (.fin k) (act (.fin k') φ) := by
  show finRep E a (k * k') φ = finRep E a k (finRep E a k' φ)
  rw [map_mul]; rfl

theorem exists_whittaker_ne_zero_induction_bad_places (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hψ : ∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w)
    (π : CuspSub E a) (α : HeightOneSpectrum (𝓞 E) → Fin a → ℂˣ)
    (hα : ∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) (T : Finset (HeightOneSpectrum (𝓞 E))) :
    ∀ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) → ∀ g : GA E a,
      (∀ w ∉ S, w ∉ T → GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g ∈ KGL w (n := a)) → whit φ.1 g ≠ 0 →
      ∃ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) ∧
        ∃ x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, whit φ.1 x ≠ 0 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro φ hφV hφ g hg hW
    obtain ⟨k, hk1, hk2⟩ := exists_outside E a S (GeneralLinearGroup.map (pFin E) g)
    have hinv : act (.fin k) φ = φ := act_fin_eq_of_outside E a φ (π.cusp φ hφV).1 S hφ k
      (fun w hw => by rw [hk1 w hw, map_pLoc_pFin]; exact hg w hw (Finset.notMem_empty w)) hk2
    refine ⟨φ, hφV, hφ, g * (finGL E a k)⁻¹, fun w hw => ?_, ?_⟩
    · rw [map_mul, map_inv, comp_finGL, hk1 w hw, map_pLoc_pFin, mul_inv_cancel]
    · have e : g = g * (finGL E a k)⁻¹ * finGL E a k := by group
      rw [e, ← whit_act_fin, hinv] at hW
      exact hW
  | insert w T hwT ih =>
    intro φ hφV hφ g hg hW
    by_cases hwS : w ∈ S
    · refine ih φ hφV hφ g (fun v hv hvT => hg v hv ?_) hW
      rw [Finset.mem_insert, not_or]
      exact ⟨fun h => hv (h ▸ hwS), hvT⟩
    obtain ⟨ϖ0, hϖ0⟩ := exists_isUnifV (E := E) w
    have hne : ϖ0 ≠ 0 := fun h => by simp [IsUnifV, h] at hϖ0
    let ϖ : (w.adicCompletion E)ˣ := Units.mk0 ϖ0 hne
    have hϖ : IsUnifV E w (ϖ : w.adicCompletion E) := hϖ0
    let gw := GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g
    obtain ⟨u, hu, N, l, k, hk, hdec⟩ := local_decomp E a w ϖ hϖ gw
    let z := GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ : Fin a => N)
    let d := GlobalTheory.JSW.diagPow ϖ l
    let F : GL (Fin a) (w.adicCompletion E) →* GA E a := (finGL E a).comp (locGL E a w)
    have hF : ∀ h, F h = finGL E a (locGL E a w h) := fun h => rfl
    let y := g * (F gw)⁻¹
    have hyw : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y = 1 := by
      show GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (g * (finGL E a (locGL E a w gw))⁻¹) = 1
      rw [map_mul, map_inv, comp_finGL, pLoc_locGL]; exact mul_inv_cancel _
    have hyv : ∀ v, v ≠ w → GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) y =
        GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g := by
      intro v hv
      show GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (g * (finGL E a (locGL E a w gw))⁻¹) = _
      rw [map_mul, map_inv, comp_finGL, pLoc_locGL_of_ne hv, inv_one, mul_one]
    have hg' : g = y * F u * F z * F d * F k := by
      have : F gw = F u * F z * F d * F k := by
        rw [hdec, map_mul, map_mul, map_mul]
      calc g = y * F gw := by simp only [y]; group
        _ = _ := by rw [this]; simp only [mul_assoc]
    have hcont : Continuous φ.1 := (π.cusp _ hφV).1.continuous
    have hleft : AutomorphicForm.IsLeftInvariant φ.1 := fun γ x => by
      rw [show AdelicGLn.diagonal E a γ = ratGL E a γ from Units.ext (Matrix.ext fun _ _ => rfl)]
      exact (π.cusp _ hφV).1.left γ x

    have h1 : whit φ.1 (y * F u * F z * F d) ≠ 0 := by
      rw [hg', hF k, ← whit_act_fin, hφ w hwS k hk] at hW
      exact hW

    have h2 : whit φ.1 (y * F z * F d) ≠ 0 := by
      have e : y * F u * F z * F d = F u * (y * F z * F d) := by
        rw [hF u, commute_finGL_locGL w hyw u]; group
      rw [e, hF u, finGL_locGL_eq_uGL w hu, whit, whittaker_uGL_mul hcont hleft] at h1
      exact right_ne_zero_of_mul h1

    let φ₁ := act (.fin (locGL E a w z)) φ
    have hφ₁V : φ₁ ∈ π.V := π.stable _ φ hφV
    have hφ₁ : ∀ v ∉ S, ∀ k' ∈ KGL v (n := a), act (.fin (locGL E a v k')) φ₁ = φ₁ := by
      intro v hv k' hk'
      have hc : locGL E a v k' * locGL E a w z = locGL E a w z * locGL E a v k' := by
        by_cases hvw : v = w
        · subst hvw; rw [← map_mul, ← map_mul, diagPow_const_comm]
        · exact (GlobalTheory.CuspRep.LocSph.comm_locGL v (locGL E a w z) (pLoc_locGL_of_ne hvw z) k').symm
      simp only [φ₁]
      rw [← act_fin_mul, hc, act_fin_mul, hφ v hv k' hk']
    have h3 : whit φ₁.1 (y * F d) ≠ 0 := by
      have e : y * F z * F d = y * F d * F z := by
        rw [mul_assoc y (F z), mul_assoc y (F d), ← map_mul, ← map_mul, diagPow_const_comm]
      rw [e, hF z, ← whit_act_fin] at h2
      exact h2
    have h4 : whit φ₁.1 y ≠ 0 := by
      have := GlobalTheory.JSW.whit_mul_locGL_diagPow E a π w (α w) (hψ w hwS) (hα w hwS) φ₁ hφ₁V (hφ₁ w hwS) y hyw ϖ hϖ l
      rw [hF d] at h3
      rw [this] at h3
      exact right_ne_zero_of_mul h3
    refine ih φ₁ hφ₁V hφ₁ y (fun v hv hvT => ?_) h4
    by_cases hvw : v = w
    · subst hvw; rw [hyw]; exact one_mem _
    · rw [hyv v hvw]
      exact hg v hv (by rw [Finset.mem_insert, not_or]; exact ⟨hvw, hvT⟩)

theorem exists_sph_whit_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → ∀ (π : CuspSub E (m + 1)) (α : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∃ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), act (.fin (locGL E (m + 1) w k)) φ = φ) ∧ ∃ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 x ≠ 0 := by
  intro E _ _ _ m S hψ π α hα
  obtain ⟨φ₀, hφ₀V, hφ₀0, hφ₀K⟩ := GlobalTheory.T.exists_global_spherical_vector_of_satake_family E (m + 1) π S (fun w => Finset.univ.val.map (α w)) hα
  obtain ⟨g, hg⟩ : ∃ g, whit φ₀.1 g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ₀0 (_root_.GlobalTheory.JSW.eq_zero_of_whit_eq_zero E (m + 1) φ₀ (π.cusp φ₀ hφ₀V) h)
  have hfin := finite_bad E (m + 1) (GeneralLinearGroup.map (pFin E) g)
  refine exists_whittaker_ne_zero_induction_bad_places S hψ π α hα hfin.toFinset φ₀ hφ₀V hφ₀K g (fun w _ hwT => ?_) hg
  by_contra h
  refine hwT (hfin.mem_toFinset.2 ?_)
  show GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) ∉ KGL w (n := (m + 1))
  rw [map_pLoc_pFin]; exact h

end GlobalTheory.JSW.NzSph
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCentreFunctionFieldPlaceCurve
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem existsUnique_centre : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ p : Place k E, ∃! b : Sp p.O ⟶ C, spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x := by
  intro k K E _ _ _ _ _ _ _ _ _ _ C _ x hx p
  obtain ⟨⟨-, hproj, -⟩, -, hxs⟩ := hx
  have hprop : IsProper (strHom k (X := C)) := (isProper_and_exists_isAmpleLB_of_isProjOver hproj).1
  have hk : ∀ c : k, algebraMap k E c ∈ p.O := by
    intro c
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hc : c = 0
    · simp [hc]
    · rw [p.2.2 c hc]
  let ik : k →+* p.O := (algebraMap k E).codRestrict p.O hk
  have hik : p.O.subtype.comp ik = algebraMap k E := RingHom.ext fun _ => rfl
  have hsq : (spMap (algebraMap K E) ≫ x) ≫ strHom k C = spMap (algebraMap p.O E) ≫ spMap ik := by
    rw [Category.assoc, hxs, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
    rfl
  have hv : ValuativeCriterion (strHom k C) := by
    rw [IsProper.eq_valuativeCriterion] at hprop
    exact hprop.1.1.1
  let S : ValuativeCommSq (strHom k C) :=
    { R := p.O, K := E, i₁ := spMap (algebraMap K E) ≫ x, i₂ := spMap ik, commSq := ⟨hsq⟩ }
  obtain ⟨U⟩ := hv S

  have hover : ∀ b : Sp p.O ⟶ C, spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x → b ≫ strHom k C = spMap ik := by
    intro b hb
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (b ≫ strHom k C)
    have e : Spec.map (φ ≫ CommRingCat.ofHom p.O.subtype) = Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
      rw [Spec.map_comp, hφ, ← Category.assoc, hb, Category.assoc, hxs, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq]
    have e2 := Spec.map_injective e
    rw [← hφ]
    congr 1
    ext c
    exact congrArg (fun f => (CommRingCat.Hom.hom f) c) e2
  refine ⟨U.default.l, U.default.fac_left, fun b hb => ?_⟩
  let L : S.commSq.LiftStruct := { l := b, fac_left := hb, fac_right := hover b hb }
  exact congrArg CommSq.LiftStruct.l (U.uniq L)

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteImageTateModuleOfBoundedExponentComm
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Proof.FiniteInertiaImage

theorem galTate_eq_of_agree {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A]
    [IsCommMonObj A] (l : ℕ) [Fact l.Prime] (I : Subgroup (Ω ≃ₐ[K] Ω)) (E : ℕ) (hE0 : 0 < E)
    (hE : ∀ σ ∈ I, galTate A l σ ^ E = 1) {σ τ : Ω ≃ₐ[K] Ω} (hσ : σ ∈ I) (hτ : τ ∈ I)
    (h : ∀ x : ptOver K Ω ⟶ A, x ^ (l ^ 2) = 1 → galPts A σ x = galPts A τ x) :
    galTate A l σ = galTate A l τ := by
  have hu : galTate A l (σ * τ⁻¹) = 1 := by
    refine _root_.GlobalTheory.HTLat.Tate.eq_one_of_pow_eq_one_of_lev_two l (ptOver K Ω ⟶ A) _ E hE0 (hE _ (I.mul_mem hσ (I.inv_mem hτ))) fun t => ?_
    rw [lev_galTate]
    have hy : galPts A τ⁻¹ (t.lev 2) ^ (l ^ 2) = 1 := by rw [← map_pow, t.lev_pow, map_one]
    have e1 : galPts A (σ * τ⁻¹) (t.lev 2) = galPts A σ (galPts A τ⁻¹ (t.lev 2)) := by
      change specAut (σ * τ⁻¹) ≫ t.lev 2 = specAut σ ≫ specAut τ⁻¹ ≫ t.lev 2
      rw [specAut_mul, Category.assoc]
    have e2 : galPts A τ (galPts A τ⁻¹ (t.lev 2)) = t.lev 2 := by
      change specAut τ ≫ specAut τ⁻¹ ≫ t.lev 2 = t.lev 2
      rw [← Category.assoc, ← specAut_mul, mul_inv_cancel, specAut_one, Category.id_comp]
    rw [e1, h _ hy, e2]
  calc galTate A l σ = galTate A l (σ * τ⁻¹ * τ) := by rw [inv_mul_cancel_right]
    _ = galTate A l τ := by rw [map_mul, hu, _root_.one_mul]

theorem finite_image_galTate : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A]
    [IsCommMonObj A] (l : ℕ) [Fact l.Prime] (I : Subgroup (Ω ≃ₐ[K] Ω)),
    Finite {x : ptOver K Ω ⟶ A // x ^ (l ^ 2) = 1} →
    (∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ) →
    (∃ E : ℕ, 0 < E ∧ ∀ σ ∈ I, galTate A l σ ^ E = 1) →
    (galTate A l '' (I : Set (Ω ≃ₐ[K] Ω))).Finite := by
  intro K Ω _ _ _ A _ _ l _ I hS _ ⟨E, hE0, hE⟩
  let S := {x : ptOver K Ω ⟶ A // x ^ (l ^ 2) = 1}
  have hmap : ∀ (σ : Ω ≃ₐ[K] Ω) (x : S), galPts A σ x.1 ^ (l ^ 2) = 1 := fun σ x => by
    rw [← map_pow, x.2, map_one]
  let g : (Ω ≃ₐ[K] Ω) → S → S := fun σ x => ⟨galPts A σ x.1, hmap σ x⟩
  let F : galTate A l '' (I : Set (Ω ≃ₐ[K] Ω)) → S → S := fun u => g u.2.choose
  have hF : Function.Injective F := by
    rintro ⟨u, hu⟩ ⟨u', hu'⟩ e
    have h1 := hu.choose_spec
    have h2 := hu'.choose_spec
    refine Subtype.ext ?_
    change u = u'
    rw [← h1.2, ← h2.2]
    refine galTate_eq_of_agree A l I E hE0 hE h1.1 h2.1 fun x hx => ?_
    have := congrFun e ⟨x, hx⟩
    exact congrArg Subtype.val this
  exact Set.finite_coe_iff.1 (Finite.of_injective F hF)

end GlobalTheory.Proof.FiniteInertiaImage
end

