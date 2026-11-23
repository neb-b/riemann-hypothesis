module

public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0019
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle0003
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0004
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0045
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasMain
public import Development.WeilBound.CoreStatements.LocalThetaKernels.LocpairAlg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.HermCpt
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CompanionTheory.CMAdele Dense PositivityTheory.ThKF
open PositivityTheory.ThK (kc_ring adele_t2Space kc_smul kc_closedU kc_cont_mat isCompact_of_units)
open GlobalTheory.CompanionTheory.SW.Core (Oh)

attribute [local instance] kc_ring adele_t2Space kc_smul

namespace Herm

theorem map_star_mul' {a b c : Type} [Fintype b] (x : Matrix a b ℂ) (y : Matrix b c ℂ) :
    (x * y).map star = x.map star * y.map star := Matrix.map_mul (f := starRingEnd ℂ)

theorem cpt_sig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) (h0 : min r s = 0) :
    ∃ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C ∧ ∀ g, gᵀ * M * g.map star = M → g ∈ C := by
  obtain ⟨hn, A, hA⟩ := h
  obtain ⟨ε, e1, e2⟩ : ∃ ε : ℂ, ε * ε = 1 ∧ Aᵀ * M * A.map star = ε • 1 := by
    rcases Nat.min_eq_zero_iff.1 h0 with rfl | rfl
    · refine ⟨-1, by simp, hA.trans ?_⟩
      ext (i | i) (j | j) <;> first | exact i.elim0 | exact j.elim0 | (simp only [Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, neg_smul, one_smul, Matrix.one_apply, Sum.inr.injEq])
    · refine ⟨1, by simp, hA.trans ?_⟩
      ext (i | i) (j | j) <;> first | exact i.elim0 | exact j.elim0 | simp [Matrix.one_apply]
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ, Aᵀ * N = (1 : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) := ⟨ε • (M * A.map star), by rw [Matrix.mul_smul, ← Matrix.mul_assoc, e2, smul_smul, e1, one_smul]⟩
  have hN' : N * Aᵀ = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hn])).1 hN
  have h1 : A * Nᵀ = 1 := by simpa using congrArg Matrix.transpose hN'
  have h2 : A.map star * Nᵀ.map star = 1 := by rw [← map_star_mul', h1]; simp
  refine ⟨(fun u : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ => A * u * Nᵀ) '' Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall 0 1,
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _).image
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const), fun g hg =>
    ⟨Nᵀ * g * A, fun k _ i _ => ?_, by
      simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]; rw [Matrix.mul_assoc, h1, Matrix.mul_one]⟩⟩
  have e3 : N * Nᵀ.map star = ε • M := by
    have : N * (Aᵀ * M * A.map star) * Nᵀ.map star = M := by
      simp only [← Matrix.mul_assoc, hN', Matrix.one_mul]; rw [Matrix.mul_assoc, h2, Matrix.mul_one]
    rw [← this, e2, Matrix.mul_smul, Matrix.smul_mul, smul_smul, e1, one_smul, Matrix.mul_one]
  have e4 : (Nᵀ * g * A)ᵀ * (Nᵀ * g * A).map star = 1 := by
    calc _ = Aᵀ * (gᵀ * (N * Nᵀ.map star) * g.map star) * A.map star := by
          simp only [map_star_mul', Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = 1 := by rw [e3, Matrix.mul_smul, Matrix.smul_mul, hg, Matrix.mul_smul, Matrix.smul_mul, e2, smul_smul, e1, one_smul]
  generalize Nᵀ * g * A = u at e4
  have e5 : ∑ l, ‖u l i‖ ^ 2 = 1 := by
    have := congrFun (congrFun e4 i) i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply_eq, Complex.star_def,
      Complex.mul_conj'] at this
    exact_mod_cast this
  rw [mem_closedBall_zero_iff, ← sq_le_one_iff₀ (norm_nonneg _), ← e5]
  exact Finset.single_le_sum (f := fun l => ‖u l i‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}


variable (F) in
def fA : Af F →+ AF F := AddMonoidHom.inr (Ainf F) (Af F)

theorem fA_mul (x : Af F) (a : AF F) : fA F x * a = fA F (x * a.2) := Prod.ext (zero_mul _) rfl

theorem cont_realAd : Continuous (realAd F) := by
  refine Continuous.prodMk (Continuous.comp (g := (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm) (continuous_pi fun v => ?_)
    (continuous_algebraMap ℝ _)) continuous_const
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem exists_arch_section (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ T : (InfinitePlace F → ℂ) → AE F E, Continuous T ∧ ∀ a, a = T (fun w => piInf (τ w) a) + fA F 1 • a := by
  choose x x1 x2 using GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h τ
  have sm : ∀ w (t : AF F) (a : AE F E), piInf (τ w) (t • a) =
      InfinitePlace.Completion.extensionEmbedding w (evInf F w t) * piInf (τ w) a := fun w t a => by
    rw [Algebra.smul_def, map_mul, PositivityTheory.ThKEst.LatArchPf.piInf_alg]
  refine ⟨fun z => ∑ w, (realAd F (z w).re • x (Pi.single w 1) + realAd F (z w).im • x (Pi.single w Complex.I)),
    continuous_finsetSum _ fun w _ =>
      by have := cont_realAd (F := F); fun_prop, fun a => ?_⟩
  rw [← sub_eq_iff_eq_add, ← sub_eq_zero]
  refine eq_zero_of_piInf σ h τ _ (fun c hc => ?_) fun w => ?_
  · have h1 : c.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hc
    have h2 : c * fA F 1 = c := Prod.ext ((mul_zero _).trans h1.symm) (mul_one _)
    have h3 : ∀ t z, c • realAd F t • x z = 0 := fun t z => by rw [smul_comm, x1 _ c hc, smul_zero]
    rw [smul_sub, smul_sub, smul_smul c, h2]
    simp only [sub_self, Finset.smul_sum, smul_add, h3, add_zero, Finset.sum_const_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sub, map_sum, map_add (f := _), sm, x2, PositivityTheory.ThKEst.LatArchPf.emb_realAd h.1]
      rw [show evInf F w (fA F 1) = 0 from rfl, Finset.sum_eq_single w (fun v _ hv => by simp [Pi.single_eq_of_ne hv.symm])
        (by simp)]
      simp


variable (F E) in
def lamF : AddSubgroup (AE F E) where
  carrier := (fun x : Ix E → Af F => ∑ i, fA F (x i) • bA F i) '' Set.univ.pi fun _ => Oh F
  zero_mem' := ⟨0, fun _ _ v => zero_mem _, Finset.sum_eq_zero fun _ _ => by simp⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    refine ⟨x + y, fun i _ v => add_mem (hx i trivial v) (hy i trivial v), ?_⟩
    simp [Finset.sum_add_distrib, add_smul]
  neg_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨-x, fun i _ v => neg_mem (hx i trivial v), ?_⟩
    simp

theorem lamF_mul {a b : AE F E} (ha : a ∈ lamF F E) (hb : b ∈ lamF F E) : a * b ∈ lamF F E := by
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  rw [Finset.sum_mul_sum]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  obtain ⟨c, hc⟩ := bA_mul (F := F) i j
  rw [smul_mul_smul_comm, hc, Finset.smul_sum]
  refine sum_mem fun k _ => ?_
  rw [smul_comm]
  refine zsmul_mem (⟨Pi.single k (x i * y j), fun l _ v => ?_, ?_⟩ : _ ∈ lamF F E) _
  · by_cases h : l = k
    · subst h; rw [Pi.single_eq_same]; exact mul_mem (hx i trivial v) (hy j trivial v)
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  · refine (Finset.sum_eq_single k (fun l _ h => by simp [Pi.single_eq_of_ne h]) (by simp)).trans ?_
    rw [Pi.single_eq_same, fA_mul]
    rfl

theorem lamF_cpt : IsCompact (lamF F E : Set (AE F E)) :=
  (isCompact_univ_pi fun _ => GlobalTheory.CompanionTheory.SW.Core.AfTop.isCompact_Oh F).image (continuous_finsetSum _ fun i _ =>
    Continuous.fun_smul (f := fun x : Ix E → Af F => fA F (x i)) (continuous_const.prodMk (continuous_apply i))
      continuous_const)

theorem lamF_nhds : ∀ᶠ a in 𝓝 (0 : AE F E), fA F 1 • a ∈ lamF F E := by
  obtain ⟨S, hS⟩ := exists_sectionC (F := F) (E := E)
  have hSc : Continuous S := IsModuleTopology.continuous_of_linearMap S
  have : ∀ᶠ a in 𝓝 (0 : AE F E), ∀ i, (S a i).2 ∈ Oh F := eventually_all.2 fun i =>
    (continuous_snd.comp ((continuous_apply i).comp hSc)).continuousAt.eventually_mem
      ((GlobalTheory.CompanionTheory.SW.Core.AfTop.isOpen_Oh F).mem_nhds (show (S 0 i).2 ∈ Oh F by rw [map_zero]; exact fun v => zero_mem _))
  refine this.mono fun a ha => ⟨fun i => (S a i).2, fun i _ => ha i, ?_⟩
  conv_rhs => rw [← hS a, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [smul_smul, fA_mul, one_mul]

def kInt (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) : Subgroup (UA σ J) where
  carrier := {g | ∀ i j, fA F 1 • (mat g - 1) i j ∈ lamF F E ∧
    fA F 1 • (mat g⁻¹ - 1) i j ∈ lamF F E}
  one_mem' := fun i j => by simp [mat_one']
  mul_mem' := fun {g h} hg hh => by
    have key : ∀ A B : Matrix (Fin n) (Fin n) (AE F E), (∀ i j, fA F 1 • (A - 1) i j ∈ lamF F E) →
        (∀ i j, fA F 1 • (B - 1) i j ∈ lamF F E) →
        ∀ i j, fA F 1 • (A * B - 1) i j ∈ lamF F E := fun A B hA hB i j => by
      have e : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
      have e2 : fA F 1 * fA F 1 = fA F 1 := Prod.ext (mul_zero _) (mul_one _)
      rw [e, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply, smul_add, smul_add, Finset.smul_sum]
      refine add_mem (add_mem (sum_mem fun k _ => ?_) (hA i j)) (hB i j)
      rw [← e2, ← smul_mul_smul_comm]
      exact lamF_mul (hA i k) (hB k j)
    refine fun i j => ⟨key _ _ (fun i j => (hg i j).1) (fun i j => (hh i j).1) i j, ?_⟩
    rw [mul_inv_rev]
    exact key _ _ (fun i j => (hh i j).2) (fun i j => (hg i j).2) i j
  inv_mem' := fun {g} hg i j => ⟨(hg i j).2, by rw [inv_inv]; exact (hg i j).1⟩

theorem kInt_open (J : Matrix (Fin n) (Fin n) E) : IsOpen (kInt σ J : Set (UA σ J)) := by
  have hm := kc_cont_mat (σ := σ) J
  refine (kInt σ J).isOpen_of_mem_nhds (g := 1) (show ∀ᶠ g in 𝓝 1, ∀ i j, _ from
    eventually_all.2 fun i => eventually_all.2 fun j => Eventually.and ?_ ?_)
  · exact (((hm.sub continuous_const).matrix_elem i j).tendsto' 1 0 (by simp [mat_one'])).eventually lamF_nhds
  · exact ((((hm.comp continuous_inv).sub continuous_const).matrix_elem i j).tendsto' 1 0 (by simp [mat_one'])).eventually lamF_nhds

end Herm

open Herm in
theorem cptOpen : CptOpen := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY h0
  refine ⟨kInt σ Y.J, kInt_open _, ?_⟩
  have : ∀ w, ∃ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C ∧ ∀ g : UA σ Y.J, (mat g).map (piInf (B.emb w)) ∈ C := fun w => by
    have e : ∀ g : UA σ Y.J, ((mat g).map (piInf (B.emb w)))ᵀ * Y.J.map (B.emb w).1 * ((mat g).map (piInf (B.emb w))).map star =
        Y.J.map (B.emb w).1 := fun g => by
      have := congrArg (·.map (piInf (B.emb w))) (show (mat g)ᵀ * incM F Y.J * (mat g).map (cA σ) = incM F Y.J from g.2)
      simp only [Matrix.map_mul, map_incM, Matrix.transpose_map] at this
      convert this using 2
      ext i j
      exact (piInf_cA hB.cm _ _).symm
    rcases hY with h | h
    · exact (cpt_sig (h.sig w) h0).imp fun C hC => ⟨hC.1, fun g => hC.2 _ (e g)⟩
    · exact (cpt_sig (h.sig w) h0).imp fun C hC => ⟨hC.1, fun g => hC.2 _ (by rw [Matrix.mul_smul, Matrix.smul_mul, e])⟩
  choose C h1 h2 using this
  obtain ⟨T, t1, t2⟩ := exists_arch_section hB.cm B.emb
  let f : (InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) × Matrix (Fin n) (Fin n) (AE F E) → Matrix (Fin n) (Fin n) (AE F E) :=
    fun p i j => T (fun w => p.1 w i j) + (p.2 i j + fA F 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) i j)
  have cf : Continuous f := continuous_matrix fun i j =>
    (t1.comp (continuous_pi fun w => ((continuous_apply w).comp continuous_fst).matrix_elem i j)).add
      ((continuous_snd.matrix_elem i j).add continuous_const)
  have key : ∀ g ∈ kInt σ Y.J, mat g ∈ f '' (Set.univ.pi C ×ˢ Set.univ.pi fun _ => Set.univ.pi fun _ => (lamF F E : Set _)) :=
    fun g hg => ⟨(fun w => (mat g).map (piInf (B.emb w)), fun i j => fA F 1 • (mat g - 1) i j),
      ⟨fun w _ => h2 w g, fun i _ j _ => (hg i j).1⟩, by
        ext i j
        simp only [f, Matrix.sub_apply, ← smul_add, sub_add_cancel, Matrix.map_apply]
        exact (t2 _).symm⟩
  exact isCompact_of_units _ (kc_closedU Y.J) _ ((kInt σ Y.J).isClosed_of_isOpen (kInt_open _)) _
    (((isCompact_univ_pi h1).prod (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => lamF_cpt)).image cf)
    fun k hk => ⟨key k hk, key k⁻¹ (inv_mem hk)⟩

theorem hermLine_of' (hC : CptAll) (hS : PairsStable) (hJ : PairsIrr) (hF : Factor) (hN : NonZeroAn)
    (hW : WeilConv) (hB : ThetaBasic) (hI : PositivityTheory.ThKF.ICont) (hM : MatchEx) : HermLine :=
  hermLine_of hC cptOpen polRank hS hJ hF hN hW hB hI hM

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.LocUnrInertA
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Inert

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.LFun.InertChart PositivityTheory.ThK PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locpair PositivityTheory.ThKH.Locrep
open GlobalTheory.EmbChart (atPlace evFin_atPlace atPlace_mul_right tensAt)
open GlobalTheory.Doubling (absE)

section Alg

variable {L : Type} [CommRing L] {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

def conjM {A : Matrix β γ L} {A' : Matrix γ β L} (h1 : A * A' = 1) (h2 : A' * A = 1) : Matrix γ γ L →* Matrix β β L where
  toFun m := A * m * A'
  map_one' := by rw [Matrix.mul_one, h1]
  map_mul' a b := by
    rw [show A * a * A' * (A * b * A') = A * (a * (A' * A) * b) * A' by simp only [Matrix.mul_assoc], h2, Matrix.mul_one]

theorem iso_iff (c : L →+* L) {A : Matrix β γ L} {A' : Matrix γ β L} (h1 : A * A' = 1) {J : Matrix β β L} {H : Matrix γ γ L}
    (hH : cT c A * Jᵀ * A = H) (M : Matrix β β L) :
    Mᵀ * J * M.map c = J ↔ cT c (A' * M * A) * H * (A' * M * A) = H := by
  have e : cT c (A' * M * A) * H * (A' * M * A) = cT c A * (Mᵀ * J * M.map c)ᵀ * A := by
    have : A * (A' * M * A) = M * A := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    calc _ = cT c (A * (A' * M * A)) * Jᵀ * (A * (A' * M * A)) := by rw [← hH, cT_mul c A]; simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [this, cT_mul]
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, cT]
  have k : ∀ X : Matrix β β L, cT c A' * (cT c A * X * A) * A' = X := fun X => by
    calc _ = cT c (A * A') * X * (A * A') := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, cT_one, Matrix.one_mul, Matrix.mul_one]
  rw [e, ← hH]
  exact ⟨fun h => by rw [h], fun h => Matrix.transpose_injective ((k _).symm.trans ((congrArg (cT c A' * · * A') h).trans (k _)))⟩

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} {Y : Spc F E n}

omit [NumberField E] in
theorem latW_le : latW Y v ≤ latHat Y := AddSubgroup.closure_mono (by
  rintro _ ⟨a, ha, hi, x, hx, rfl⟩
  have e : a = atPlace v (evFin F v a) := by simpa [atPlace_mul_right] using (idem_smul ha).symm
  refine ⟨a, by rw [e]; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F), fun u => ?_, x, hx, rfl⟩
  by_cases hu : u = v
  · exact hu ▸ hi
  · rw [e, show evFin F u (atPlace v (evFin F v a)) = 0 from evalV_singleFin_ne hu _]; exact zero_mem _)

omit [NumberField E] in
theorem idem_mem {z : Fin n → AE F E} (hz : z ∈ latHat Y) : atPlace v (1 : Fv F v) • z ∈ latW Y v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, hi, x, hx, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨atPlace v 1 • a, at_smul_idem v a, by
      rw [smul_eq_mul, map_mul, evFin_atPlace, one_mul]; exact hi v, x, hx, by rw [smul_smul]; rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | neg a _ ha => rw [smul_neg]; exact neg_mem ha

omit [NumberField E] in
theorem stab_latW {g : Matrix (Fin n) (Fin n) (AE F E)} (hat : ∀ z ∈ latW Y v, At (evFin F v) z) :
    (∀ z ∈ latHat Y, At (evFin F v) z → g *ᵥ z ∈ latHat Y) ↔ ∀ z ∈ latW Y v, g *ᵥ z ∈ latW Y v :=
  ⟨fun h z hz => idem_smul (at_mulVec_right g (hat z hz)) ▸ idem_mem (h z (latW_le hz) (hat z hz)),
    fun h z hz ha => latW_le (h z (idem_smul ha ▸ idem_mem hz))⟩

omit [NumberField E] in
theorem mulVec_latHat {N : Matrix (Fin n) (Fin n) (AE F E)} (hN : At (evFin F v) N) (h : ∀ z ∈ latW Y v, N *ᵥ z ∈ latW Y v)
    {z : Fin n → AE F E} (hz : z ∈ latHat Y) : N *ᵥ z ∈ latHat Y := by
  have := latW_le (h _ (idem_mem hz))
  rwa [Matrix.mulVec_smul, idem_smul (at_mulVec_left hN z)] at this

omit [NumberField E] in
theorem piInf_at {u : InfinitePlace F} (τ : EmbOver E u) {z : AE F E} (hz : At (evFin F v) z) : piInf τ z = 0 := by
  have h0 : compInf F E u (algebraMap (AF F) (AE F E) (atPlace v 1)) = 0 :=
    (congrArg (· ⊗ₜ[F] _) (show evInf F u (atPlace v 1) = 0 from rfl)).trans (TensorProduct.zero_tmul _ _)
  rw [← idem_smul hz, Algebra.smul_def, piInf, RingHom.comp_apply, map_mul, h0, zero_mul, map_zero]

theorem mem_K {B : Base F E} {K : Subgroup (G2 σ Y)} (hK : IsStab2 B K) {k : G2 σ Y}
    (h : ∀ x ∈ ({k, k⁻¹} : Set (G2 σ Y)), At (evFin F v) (mat2 x - 1) ∧ ∀ i j : Fin n → Fin n ⊕ Fin n, i ∈ ({.inl, .inr} : Set _) →
      j ∈ ({.inl, .inr} : Set _) → ∀ z ∈ latW Y v, (mat2 x - 1).submatrix i j *ᵥ z ∈ latW Y v) : k ∈ K := by
  refine (hK k).2 ⟨fun u => ?_, fun z z' hz hz' x hx => ?_⟩
  · have : (mat2 k).map (piInf (B.emb u)) = 1 := Matrix.ext fun i j => by
      have := piInf_at (B.emb u) (z := (mat2 k - 1) i j) fun a ha => congrFun (congrFun ((h k (by simp)).1 a ha) i) j
      rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
      simpa [Matrix.one_apply, apply_ite] using this
    rw [this]; exact Commute.one_left _
  · obtain ⟨h1, h2⟩ := h x hx
    have key : ∀ i : Fin n → Fin n ⊕ Fin n, i ∈ ({.inl, .inr} : Set _) → Sum.elim z z' ∘ i ∈ latHat Y →
        (mat2 x *ᵥ Sum.elim z z') ∘ i ∈ latHat Y := fun i hi h3 => by
      have b : ∀ j : Fin n → Fin n ⊕ Fin n, At (evFin F v) ((mat2 x - 1).submatrix i j) := fun j a ha =>
        Matrix.ext fun _ _ => congrFun (congrFun (h1 a ha) _) _
      convert add_mem h3 (add_mem (mulVec_latHat (b .inl) (h2 i _ hi (by simp)) hz) (mulVec_latHat (b .inr) (h2 i _ hi (by simp)) hz'))
      have : mat2 x *ᵥ Sum.elim z z' = Sum.elim z z' + (mat2 x - 1) *ᵥ Sum.elim z z' := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
      rw [this]
      ext l
      simp [Matrix.mulVec, dotProduct]
    exact ⟨key _ (by simp) hz, key _ (by simp) hz'⟩

variable (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]


variable (β) in
def up : Matrix β β (w.adicCompletion E) →* Matrix β β (AE F E) :=
  (liftM E v β).comp (RingHom.mapMatrix (complEquiv hw h).symm.toRingHom).toMonoidHom

theorem up_pi (m : Matrix β β (w.adicCompletion E)) : (up hw h β m).map (piE h) = m := Matrix.ext fun i j =>
  (congrArg (toCompl h) (congrFun (congrFun (comp_liftM v _) i) j)).trans ((complEquiv hw h).apply_symm_apply _)

theorem up_aw (m : Matrix β β (w.adicCompletion E)) : (up hw h β m).map (aw E v) = 1 := aw_liftM v _

theorem up_at (m : Matrix β β (w.adicCompletion E)) : At (evFin F v) (up hw h β m - 1) := at_liftM v _

include hw in
theorem extW {ι κ : Type} {a b : Matrix ι κ (AE F E)} (h1 : a.map (piE h) = b.map (piE h)) (h2 : a.map (aw E v) = b.map (aw E v)) :
    a = b := extM v (Matrix.ext fun i j => (toCompl_bijective hw h).1 (congrFun (congrFun h1 i) j)) h2

theorem continuous_tensAt : Continuous (tensAt E v : Ev E v → AE F E) := by
  haveI : IsModuleTopology (Fv F v) (Ev E v) := ⟨rfl⟩
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  let b := Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)
  have e : (tensAt E v : Ev E v → AE F E) = fun y => ∑ i, atPlace v (b.coord i y) • tensAt E v (b i) := by
    funext y
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr y, map_sum]
    exact Finset.sum_congr rfl fun i _ => smul_tensAt v _ _
  rw [e]
  exact continuous_finsetSum _ fun i _ => ((GlobalTheory.VacAny.continuous_atPlace v).comp
    (IsModuleTopology.continuous_of_linearMap (b.coord i))).smul continuous_const

theorem continuous_up : Continuous (up hw h β) := by
  haveI : IsModuleTopology (Fv F v) (Ev E v) := ⟨rfl⟩
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : IsTopologicalAddGroup (Ev E v) := IsModuleTopology.topologicalAddGroup (Fv F v) _
  have c1 : Continuous (liftM E v β) :=
    continuous_const.add ((continuous_id.sub continuous_const).matrix_map continuous_tensAt)
  exact c1.comp (continuous_id.matrix_map (continuous_complEquiv hw h).2)

include hw in
theorem continuous_piE : Continuous (piE h) := (continuous_complEquiv hw h).1.comp
  (GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap (map_mul (evFin F v))
    ((RestrictedProduct.continuous_eval v).comp continuous_snd))

variable {h} {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) {J : Matrix β β (AE F E)}
  {A : Matrix β γ (w.adicCompletion E)} {A' : Matrix γ β (w.adicCompletion E)} (h1 : A * A' = 1) (h2 : A' * A = 1)
  {H : Matrix γ γ (w.adicCompletion E)} (hH : cT c A * (J.map (piE h))ᵀ * A = H)

omit [DecidableEq β] in
include hc in
theorem pi_gram (M : Matrix β β (AE F E)) :
    (Mᵀ * J * M.map (cA σ)).map (piE h) = (M.map (piE h))ᵀ * J.map (piE h) * (M.map (piE h)).map c := by
  rw [Matrix.map_mul, Matrix.map_mul]
  exact congrArg _ (Matrix.ext fun i j => piE_cA hc _)

def liftW : UJ c H →* UG (cA σ) J :=
  ((Units.map ((up hw h β).comp (conjM h1 h2))).comp (UJ c H).subtype).codRestrict _ fun g => by
    change (up hw h β (A * g.1.1 * A'))ᵀ * J * (up hw h β (A * g.1.1 * A')).map (cA σ) = J
    refine extW hw h ?_ ?_
    · rw [pi_gram hc, up_pi, iso_iff c h1 hH, show A' * (A * g.1.1 * A') * A = A' * A * g.1.1 * (A' * A) by
        simp only [Matrix.mul_assoc], h2, Matrix.one_mul, Matrix.mul_one]
      exact g.2
    · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, awM_cA, up_aw, Matrix.transpose_one,
        Matrix.map_one _ (map_zero _) (map_one _), one_mul, mul_one]

def downW : UG (cA σ) J →* UJ c H :=
  ((Units.map ((conjM h2 h1).comp (piE h).mapMatrix.toMonoidHom)).comp (UG (cA σ) J).subtype).codRestrict _ fun g =>
    (iso_iff c h1 hH _).1 ((pi_gram hc g.1.1).symm.trans (congrArg (·.map (piE h)) g.2))

theorem continuous_liftW : Continuous (liftW hw hc h1 h2 hH) :=
  ((Units.continuous_map ((continuous_up hw h).comp ((continuous_const.matrix_mul continuous_id).matrix_mul
    continuous_const))).comp continuous_subtype_val).subtype_mk _

include hw in
theorem continuous_downW : Continuous (downW hc h1 h2 hH) :=
  ((Units.continuous_map ((continuous_const.matrix_mul (continuous_id.matrix_map (continuous_piE hw h))).matrix_mul
    continuous_const)).comp continuous_subtype_val).subtype_mk _

theorem down_lift (x : UJ c H) : downW hc h1 h2 hH (liftW hw hc h1 h2 hH x) = x := Subtype.ext (Units.ext (by
  change A' * (up hw h β (A * x.1.1 * A')).map (piE h) * A = x.1.1
  rw [up_pi, show A' * (A * x.1.1 * A') * A = A' * A * x.1.1 * (A' * A) by simp only [Matrix.mul_assoc], h2, Matrix.one_mul,
    Matrix.mul_one]))

theorem lift_down {g : UG (cA σ) J} (hg : At (evFin F v) (g.1.1 - 1)) : liftW hw hc h1 h2 hH (downW hc h1 h2 hH g) = g :=
  Subtype.ext (Units.ext (mat_inj hw h (sub_sub_sub_cancel_right _ _ (1 : Matrix β β (AE F E)) ▸ at_sub (up_at hw h _) hg) (by
    refine (up_pi hw h _).trans ?_
    change A * (A' * g.1.1.map (piE h) * A) * A' = _
    rw [show ∀ M, A * (A' * M * A) * A' = A * A' * M * (A * A') from fun M => by simp only [Matrix.mul_assoc], h1, Matrix.one_mul,
      Matrix.mul_one])))

end GlobalTheory.ThK.Dbl.Inert

end
end

