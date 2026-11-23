module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SkewHermitianAdelicCoverOfAdeleCover
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv

noncomputable section

namespace GlobalTheory.Eis.Conv.CovSkew

theorem exists_delta (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) :
    ∃ δ : E, σ δ = -δ ∧ ∀ z : E, ∃ a b : F, z = a • (1 : E) + b • δ := by
  obtain ⟨-, hc, h2, hσ⟩ := h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hnr : ¬ ComplexEmbedding.IsReal τ := IsTotallyComplex.complexEmbedding_not_isReal τ
  obtain ⟨x, hx⟩ : ∃ x, star (τ x) ≠ τ x := by
    by_contra hcon
    push Not at hcon
    apply hnr
    rw [ComplexEmbedding.isReal_iff]
    ext x
    exact hcon x
  have hδ : σ (x - σ x) = -(x - σ x) := by
    apply τ.injective
    rw [hσ, map_neg, map_sub, hσ, star_sub, star_star, neg_sub]
  have h0 : x - σ x ≠ 0 := by
    intro h0
    apply hx
    rw [← hσ, ← sub_eq_zero.mp h0]
  refine ⟨x - σ x, hδ, ?_⟩
  generalize x - σ x = δ at hδ h0
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg σ hst
    have hsm : ∀ (a : F) (z : E), σ (a • z) = a • σ z := fun a z => σ.toLinearMap.map_smul a z
    rw [map_add (f := _), hsm, hsm, map_one, hδ, map_zero, smul_neg] at h1
    have hs : (2 * s) • (1 : E) = 0 := by
      rw [two_mul, add_smul]; linear_combination hst + h1
    have hs0 : s = 0 := by simpa using hs
    refine ⟨hs0, ?_⟩
    rw [hs0, zero_smul, zero_add] at hst
    exact (smul_eq_zero.mp hst).resolve_right h0
  intro z
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp [h2])
  have hz : z ∈ Submodule.span F (Set.range ![(1 : E), δ]) := by rw [hsp]; trivial
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Submodule.mem_span_pair] at hz
  obtain ⟨a, b, hab⟩ := hz
  exact ⟨a, b, hab.symm⟩

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]

theorem exists_coords (δ : E) (h : ∀ z : E, ∃ a b : F, z = a • (1 : E) + b • δ) (z : R ⊗[F] E) :
    ∃ u v : R, z = u ⊗ₜ[F] (1 : E) + v ⊗ₜ[F] δ := by
  induction z with
  | tmul r e =>
    obtain ⟨a, b, rfl⟩ := h e
    exact ⟨a • r, b • r, by
      rw [TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul]⟩
  | add x y hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    exact ⟨u + u', v + v', by simp only [TensorProduct.add_tmul]; abel⟩

def psi (δ : E) (a a' : R) : R ⊗[F] E := (a - a') • (1 : R ⊗[F] E) + (a + a') • ((1 : R) ⊗ₜ[F] δ)

theorem psi_eq (δ : E) (a a' : R) :
    psi δ a a' = (a - a') ⊗ₜ[F] (1 : E) + (a + a') ⊗ₜ[F] δ := by
  simp [psi, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']

theorem exists_psi [CharZero F] (σ : E →ₐ[F] E) (δ : E) (hδ : σ δ = -δ)
    (h : ∀ z : E, ∃ a b : F, z = a • (1 : E) + b • δ) {n : ℕ}
    (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (hS : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) S = -S) :
    ∃ T : Fin n → Fin n → R, ∀ i j, S i j = psi δ (T i j) (T j i) := by
  choose U V hUV using fun i j => exists_coords δ h (S i j)
  set c : R := algebraMap F R 2⁻¹ with hc
  have h2 : 2 * c = 1 := by
    rw [hc, ← map_ofNat (algebraMap F R) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  refine ⟨fun i j => c * c * (U i j - U j i + V i j + V j i), fun i j => ?_⟩
  have h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (S j i) = - S i j := congrFun (congrFun hS i) j
  have e1 : ∀ k l, S k l = U k l • (1 : R ⊗[F] E) + V k l • ((1 : R) ⊗ₜ[F] δ) := fun k l => by
    rw [hUV]; simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
  have e2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (S j i)
      = U j i • (1 : R ⊗[F] E) - V j i • ((1 : R) ⊗ₜ[F] δ) := by
    rw [hUV, map_add (f := _)]
    change U j i ⊗ₜ[F] σ 1 + V j i ⊗ₜ[F] σ δ = _
    simp [hδ, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.tmul_neg,
      sub_eq_add_neg]
  rw [e2] at h1
  have e3 := e1 i j
  have h2' : 2 * algebraMap R (R ⊗[F] E) c = 1 := by
    rw [← map_ofNat (algebraMap R (R ⊗[F] E)) 2, ← map_mul, h2, map_one]
  unfold psi
  simp only [Algebra.smul_def, map_add (f := _), map_sub, map_mul] at h1 e3 ⊢
  generalize algebraMap R (R ⊗[F] E) = f at *
  generalize ((1 : R) ⊗ₜ[F] δ) = d at *
  linear_combination (f c) * e3 + (f c) * h1 - S i j * h2'
    - f c * (f (U i j) - f (U j i) + (f (V i j) + f (V j i)) * d) * h2'

theorem psi_split (δ : E) (x x' : F) (y y' t w w' : R) :
    psi δ (algebraMap F R x + y + t * w) (algebraMap F R x' + y' + t * w')
      = inclR (F := F) R ((x - x') • (1 : E) + (x + x') • δ) + psi δ y y'
        + algebraMap R (R ⊗[F] E) t * psi δ w w' := by
  have : inclR (F := F) R ((x - x') • (1 : E) + (x + x') • δ)
      = psi δ (algebraMap F R x) (algebraMap F R x') := by
    rw [psi_eq, ← map_sub, ← map_add (f := _), Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.smul_tmul,
      ← TensorProduct.tmul_add]
    rfl
  rw [this]
  unfold psi
  simp only [Algebra.smul_def, map_add (f := _), map_sub, map_mul]
  ring

end

theorem cover_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (b C₀ : ℝ) (Ω₀ : Set (AF F)), IsCompact Ω₀ → (∀ m : ℕ, ∃ Y : Finset (AF F), (Y.card : ℝ) ≤ C₀ * b ^ m ∧ ∀ a : AF F, ∃ x : F, ∃ y ∈ Y, ∃ ω ∈ Ω₀, a = algebraMap F (AF F) x + y + (halfInf F).1 ^ m * ω) → ∀ n : ℕ, ∃ (Ω : Set (AF F ⊗[F] E)) (C : ℝ), IsCompact Ω ∧ ∀ m : Fin n → ℕ, ∃ Y : Finset (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ C * ∏ i, (b ^ 2) ^ (n * m i) ∧ ∀ S : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) S = -S → ∃ S₀ : Matrix (Fin n) (Fin n) E, ∃ y ∈ Y, ∃ ω : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), (∀ i j, ω i j ∈ Ω) ∧ S = S₀.map (inclR (F := F) (AF F)) + y + Matrix.diagonal (fun i => (halfE F E).1 ^ m i) * ω * Matrix.diagonal (fun i => (halfE F E).1 ^ m i) := by
  intro F E _ _ _ _ _ σ hσ b C₀ Ω₀ hΩ₀ hcov n
  classical
  obtain ⟨δ, hδ, hsp⟩ := exists_delta F E σ hσ
  choose Y hY hYc using hcov
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := isTopologicalRing_tens
  have hcont : Continuous fun p : AF F × AF F => psi (F := F) δ p.1 p.2 := by
    unfold psi
    fun_prop
  refine ⟨_, C₀ ^ (n * n), (hΩ₀.prod hΩ₀).image hcont, fun m => ?_⟩
  refine ⟨(Fintype.piFinset fun p : Fin n × Fin n => Y (m p.1 + m p.2)).image
    (fun y => Matrix.of fun i j => psi δ (y (i, j)) (y (j, i))), ?_, fun S hS => ?_⟩
  · refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
    rw [Fintype.card_piFinset, Nat.cast_prod]
    refine (Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun p _ => hY _)).trans (le_of_eq ?_)
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Finset.prod_pow_eq_pow_sum]
    congr 1
    simp only [← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum, Fintype.sum_prod_type]
    congr 1
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, ← Finset.mul_sum]
    ring
  · obtain ⟨T, hT⟩ := exists_psi σ δ hδ hsp S hS
    choose x y hy ω hω hTe using fun i j => hYc (m i + m j) (T i j)
    refine ⟨Matrix.of fun i j => (x i j - x j i) • (1 : E) + (x i j + x j i) • δ, _,
      Finset.mem_image.mpr ⟨fun p => y p.1 p.2, Fintype.mem_piFinset.mpr fun p => hy _ _, rfl⟩,
      Matrix.of fun i j => psi δ (ω i j) (ω j i),
      fun i j => ⟨(ω i j, ω j i), ⟨hω _ _, hω _ _⟩, rfl⟩, ?_⟩
    ext i j
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hT,
      hTe i j, hTe j i, add_comm (m j) (m i), psi_split]
    have : (halfE F E).1 = algebraMap (AF F) (AF F ⊗[F] E) (halfInf F).1 := rfl
    rw [this, map_pow]
    simp only [Matrix.map_apply, Matrix.of_apply]
    ring

end GlobalTheory.Eis.Conv.CovSkew

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TensorIdeleNormalizedAbsIdeleHalfAtInfinity
section
noncomputable section

namespace GlobalTheory.Eis.Conv

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.AdelicU

theorem norm_halfE (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h : Module.finrank F E = 2) :
    Algebra.norm (AF F) (halfE F E).1 = (halfInf F).1 ^ 2 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  haveI : Nontrivial (AF F) := (evInf F w).toRingHom.domain_nontrivial
  change Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) (halfInf F).1) = _
  rw [Algebra.norm_algebraMap, Module.finrank_baseChange, h]

theorem evFin_halfInf (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    evFin F v (halfInf F).1 = 1 :=
  map_one (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)

theorem evInf_halfInf (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    evInf F w (halfInf F).1 = algebraMap F _ 2⁻¹ :=
  (GlobalTheory.AutFunCompare.evW w).commutes _

theorem nnnorm_evInf_halfInf (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    ‖evInf F w (halfInf F).1‖₊ = 2⁻¹ := by
  rw [evInf_halfInf]
  have h2 : w (2⁻¹ : F) = 2⁻¹ := by
    rw [← InfinitePlace.norm_embedding_eq w, map_inv₀, norm_inv, map_ofNat]
    simp
  have e : ‖((2⁻¹ : F) : w.Completion)‖ = 2⁻¹ := (InfinitePlace.Completion.norm_coe w _).trans h2
  apply NNReal.eq
  rw [NNReal.coe_inv, NNReal.coe_ofNat]
  rw [InfinitePlace.Completion.algebraMap_apply]
  exact e

theorem absE_halfE (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) : absE F E (halfE F E) = ((4 : ℝ≥0) ^ Fintype.card (InfinitePlace F))⁻¹ := by
  haveI := h.1
  have hn := norm_halfE F E h.2.2.1
  have hfin : ∀ v, absEv F E v (unitFin F E v (halfE F E)) = 1 := fun v => by
    rw [absEv_unitFin, hn, map_pow, evFin_halfInf]
    simp
  have hinf : ∀ w, absEw F E w (unitInf F E w (halfE F E)) = 4⁻¹ := fun w => by
    rw [absEw_unitInf, hn, map_pow, nnnorm_pow, nnnorm_evInf_halfInf, InfinitePlace.mult,
      if_pos (IsTotallyReal.isReal w), pow_one, inv_pow]
    norm_num
  rw [absE_apply, finprod_eq_one_of_forall_eq_one hfin, mul_one, Finset.prod_congr rfl fun w _ => hinf w,
    Finset.prod_const, Finset.card_univ, inv_pow]

end GlobalTheory.Eis.Conv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaKernelFiniteAdelicLaws
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceIncl.KernLaws

theorem exists_finite_lift {D : D7} (V : HSp D) (q : Bridge.Gf V) : ∃ κ ∈ GfC V, fin V κ = q := by
  obtain ⟨_, g, rfl⟩ := q
  obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig V.gram
  obtain ⟨k, k1, k2⟩ := h2 1 (finHom V g)
  exact ⟨⟨k, (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ ((h1 _).1 g.2).2⟩⟩, k1, Subtype.ext k2⟩

theorem fin_mul {D : D7} (V : HSp D) (a b : GA D V) : fin V a * fin V b = fin V (a * b) :=
  (map_mul (finHom V).rangeRestrict a b).symm

theorem ratF_eq {D : D7} (V : HSp D) (γ : GQ V) : Bridge.ratF V γ = fin V γ := rfl

theorem lift_of_mem_J {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {κ : GA D V}
    (hκ : κ ∈ GfC V) (hk : fin V κ ∈ (levEnv V β L).J) :
    IsLevelLift V β L 1 κ ∧ ((((levEnv V β L).χ ⟨_, hk⟩)⁻¹ : ℂˣ) : ℂ) = (levChi V β (flagL L) κ)⁻¹ := by
  refine ⟨⟨hκ, hk.1, Subgroup.mem_bot.1 hk.2⟩, ?_⟩
  unfold levChi
  rw [← levFn_flag1, Units.val_inv_eq_inv_val]
  rfl

theorem exists_lift_J {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J) : ∃ κ, fin V κ = k ∧
    IsLevelLift V β L 1 κ ∧ ((((levEnv V β L).χ k)⁻¹ : ℂˣ) : ℂ) = (levChi V β (flagL L) κ)⁻¹ := by
  obtain ⟨k, hk⟩ := k
  obtain ⟨κ, hκ, rfl⟩ := exists_finite_lift V k
  exact ⟨κ, rfl, lift_of_mem_J V β L hκ hk⟩

theorem finE_of_fin {D : D7} (V : HSp D) {κ : GA D V} {x : Bridge.Gf V} (e : fin V κ = x) :
    finE V κ = Formalism.UG.bc (swapAE D) (x : GL _ _) := by
  have : finHom V κ = x.1 := congrArg Subtype.val e
  rw [finE_eq, this]

theorem exists_lift_Q {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).Q) : ∃ κ, fin V κ = k ∧
    IsLevelLift V β L (rTup β L (Formalism.UG.bc (swapAE D) ((k : Bridge.Gf V) : GL _ _))) κ ∧
      ((((levEnv V β L).ch k)⁻¹ : ℂˣ) : ℂ) = (levChi V β (flagL L) κ)⁻¹ := by
  obtain ⟨κ, hκ, e⟩ := exists_finite_lift V k.1
  have e' := finE_of_fin V e
  refine ⟨κ, e, ⟨hκ, ?_, congrArg (rTup β L) e'⟩, ?_⟩
  · rw [e']
    exact k.2.1
  · have e2 : (levEnv V β L).ch k = levFn β (flagL L) (finE V κ) := (congrArg (levFn β (flagL L)) e').symm
    rw [Units.val_inv_eq_inv_val, e2, levChi]

theorem lift_one {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsLevelLift V β L 1 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact rTup_one⟩

theorem exists_actL {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (g0 : G0 L.Pg L.r) (hex : ∃ κ, IsLevelLift V β L g0 κ) : ∃ κ, IsLevelLift V β L g0 κ ∧
      ∀ F h, actL V β L g0 F h = (levChi V β (flagL L) κ)⁻¹ * F (h * κ) := by
  refine ⟨hex.choose, hex.choose_spec, fun F h => ?_⟩
  change actG0 V β L g0 F h = _
  unfold actG0
  rw [dite_eq_left hex]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0)

theorem kernA_apply (h : GA D (Vc D i)) (w : (R.cV i).W) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)) :
    kernA R i t h w v g =
      Datum.thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w))) := rfl

theorem kernA_mul_real (hio : R.thP_ioP) (h : GA D (Vc D i)) {u : GA D (Vc D i)} (hu : u ∈ GinfC (Vc D i)) :
    kernA R i t (h * u) = kernA R i t h := by
  ext w v g
  rw [kernA_apply, kernA_apply]
  unfold Datum.thetaKO
  rw [show ((h * u, g) : GA D (Vc D i) × GA D (Wc D i)) = (h, g) * (u, 1) from Prod.ext rfl (mul_one g).symm,
    map_mul, Module.End.mul_apply, (hio i t).1 u hu, ← Module.End.mul_apply, ← map_mul, mul_inv_rev,
    mul_inv_cancel_left]

theorem kern_fin (hio : R.thP_ioP) (h : GA D (Vc D i)) : kern R i t (fin (Vc D i) h) = kernA R i t h := by
  unfold kern
  have e := (MonoidHom.mem_range.1 (fin (Vc D i) h).2).choose_spec
  generalize (MonoidHom.mem_range.1 (fin (Vc D i) h).2).choose = h' at e
  have hu : h⁻¹ * h' ∈ GinfC (Vc D i) := by
    change finHom (Vc D i) (h⁻¹ * h') = 1
    rw [map_mul, map_inv, e]
    exact inv_mul_cancel _
  rw [← kernA_mul_real R i t hio h hu, mul_inv_cancel_left]

theorem kernA_rat (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (γ : GQ (Vc D i)) (h : GA D (Vc D i)) (w : (R.cV i).W) :
    kernA R i t (γ * h) ((R.cV i).ρ γ w) = kernA R i t h w := by
  funext v g
  rw [kernA_apply, kernA_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right]
  have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ (hω i t) _
    (hpt i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w)))).1 γ γ.2 1 (one_mem _) h g
  rwa [one_mul] at this

theorem kernA_eigen (hθ : R.models_inf) (hc : R.models_cV) (hω : R.thP_ωP) (hpt : R.thP_pt_theta)
    {κ : GA D (Vc D i)} (hκ : κ ∈ GfC (Vc D i)) {κ' : GA D (Wc D i)} (hκ' : κ' ∈ GfC (Wc D i)) {c : ℂ}
    (e : R.ωP i t (κ, κ') (R.vP i t) = c • R.vP i t) (h : GA D (Vc D i)) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)) :
    kernA R i t (h * κ) w v (g * κ') = c * kernA R i t h w v g := by
  rw [kernA_apply, kernA_apply, mul_inv_rev, map_mul, (hc i).1 _ (inv_mem hκ), one_mul]
  exact (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ (hω i t) _ (hpt i t _)).2 κ κ' c
    (GlobalTheory.FiniteFock.om_pureTensorO_of_finite _ _ _ _ _ _ _ hθ (hω i t) _ _ _ _ _ (hpt i t) κ hκ κ' hκ' c e _) h g

theorem levChi_flag_datWp (κ' : GA D (Wc D i)) : levChi (Wc D i) (R.βW i) (flagL (R.datWp i R.triv)) κ' = 1 := by
  have h2 : ext1 (flagL (R.datWp i R.triv)).P.H (flagL (R.datWp i R.triv)).P.chi
      (rTup (R.βW i) (flagL (R.datWp i R.triv)) (finE (Wc D i) κ')) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h2, show (flagL (R.datWp i R.triv)).s = 0 from rfl, Finset.range_zero,
    show (flagL (R.datWp i R.triv)).Q = ∅ from rfl, Finset.prod_empty]
  simp only [Finset.prod_empty, Finset.prod_const_one, mul_one, Units.val_one]

theorem kern_rat (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (hio : R.thP_ioP) (γ : GQ (Vc D i)) (h : Bridge.Gf (Vc D i))
    (w : (R.cV i).W) : kern R i t (Bridge.ratF (Vc D i) γ * h) ((R.cV i).coef.ρ γ w) = kern R i t h w := by
  obtain ⟨h', -, e⟩ := exists_finite_lift (Vc D i) h
  have e1 : kern R i t (Bridge.ratF (Vc D i) γ * h) = kernA R i t (γ * h') := by
    rw [← e, ratF_eq, fin_mul, kern_fin R i t hio]
  have e2 : kern R i t h = kernA R i t h' := by rw [← e, kern_fin R i t hio]
  rw [e1, e2]
  exact kernA_rat R i t hω hpt γ h' w

theorem kern_eigen (hθ : R.models_inf) (hc : R.models_cV) (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (hio : R.thP_ioP)
    {κ : GA D (Vc D i)} (hκ : κ ∈ GfC (Vc D i)) {κ' : GA D (Wc D i)} (hκ' : κ' ∈ GfC (Wc D i)) {c : ℂ}
    (e : R.ωP i t (κ, κ') (R.vP i t) = c • R.vP i t) (h : Bridge.Gf (Vc D i)) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)) :
    kern R i t (h * fin (Vc D i) κ) w v (g * κ') = c * kern R i t h w v g := by
  obtain ⟨h', -, e0⟩ := exists_finite_lift (Vc D i) h
  have e1 : kern R i t (h * fin (Vc D i) κ) = kernA R i t (h' * κ) := by
    rw [← e0, fin_mul, kern_fin R i t hio]
  have e2 : kern R i t h = kernA R i t h' := by rw [← e0, kern_fin R i t hio]
  rw [e1, e2]
  exact kernA_eigen R i t hθ hc hω hpt hκ hκ' e h' w v g

theorem eq_smul_of_mul_one {X Y : Type} [Monoid Y] (F F' : X → Y → ℂ) (c : ℂ) (h : ∀ v g, F v (g * 1) = c * F' v g) :
    F = c • F' := by
  funext v g
  rw [← mul_one g, h, mul_one]
  rfl

theorem eq_smul_of_mul {Y : Type} [Monoid Y] (B F F' : Y → ℂ) (a c : ℂ) (y : Y) (ha : a = 1) (h1 : ∀ g, B g = a⁻¹ * F (g * y))
    (h : ∀ g, F (g * y) = c * F' g) : B = c • F' := by
  funext g
  rw [h1, ha, inv_one, one_mul, h]
  rfl

theorem kern_level (hθ : R.models_inf) (hc : R.models_cV) (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (hio : R.thP_ioP)
    (hD : DatumType R i t) (h : Bridge.Gf (Vc D i)) (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) (w : (R.cV i).W) :
    kern R i t (h * k) w = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k)⁻¹ : ℂˣ) : ℂ) • kern R i t h w := by
  obtain ⟨κ, e1, l1, e2⟩ := exists_lift_J (Vc D i) (R.βV i) (R.datVt i t) k
  rw [e2, ← e1]
  exact eq_smul_of_mul_one _ _ _ (kern_eigen R i t hθ hc hω hpt hio l1.1 (GfC (Wc D i)).one_mem
    (hD 1 κ 1 l1 (lift_one _ (R.βW i) (R.datWp i R.triv))) h w)

theorem kern_act (hθ : R.models_inf) (hc : R.models_cV) (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (hio : R.thP_ioP)
    (hD : DatumType R i t) (g0 : G0 R.Pg D.R.r) (q : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q)
    (hg : g0 = rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf (Vc D i)) : GL _ _)))
    (hex : ∃ κ', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ') (h : Bridge.Gf (Vc D i)) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 (kern R i t (h * q) w v) =
      ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch q)⁻¹ : ℂˣ) : ℂ) • kern R i t h w v := by
  refine (exists_lift_Q (Vc D i) (R.βV i) (R.datVt i t) q).elim fun κ H => ?_
  refine (exists_actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 hex).elim fun κ' H' => ?_
  have l1 : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ := ⟨H.2.1.1, H.2.1.2.1, H.2.1.2.2.trans hg.symm⟩
  have := kern_eigen R i t hθ hc hω hpt hio l1.1 H'.1.1 (hD g0 κ κ' l1 H'.1) h w v
  rw [H.2.2, ← H.1]
  exact eq_smul_of_mul _ _ _ _ _ κ' (levChi_flag_datWp R i κ') (H'.2 _) this

end GlobalTheory.TraceIncl.KernLaws

namespace GlobalTheory.TraceIncl

open KernLaws

theorem kern_laws : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0), R.models_inf → R.models_cV → R.thP_ωP → R.thP_pt_theta → R.thP_ioP → GlobalTheory.TraceIncl.DatumType R i t → (∀ h, GlobalTheory.TraceIncl.kern R i t (fin (Vc D i) h) = GlobalTheory.TraceIncl.kernA R i t h) ∧ (∀ (γ : GQ (Vc D i)) h w, GlobalTheory.TraceIncl.kern R i t (Bridge.ratF (Vc D i) γ * h) ((R.cV i).coef.ρ γ w) = GlobalTheory.TraceIncl.kern R i t h w) ∧ (∀ h (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) w, GlobalTheory.TraceIncl.kern R i t (h * k) w = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k)⁻¹ : ℂˣ) : ℂ) • GlobalTheory.TraceIncl.kern R i t h w) ∧ ∀ (g0 : G0 R.Pg D.R.r) (q : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q), g0 = rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf (Vc D i)) : GL _ _)) → (∃ κ', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ') → ∀ h w v, actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 (GlobalTheory.TraceIncl.kern R i t (h * q) w v) = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch q)⁻¹ : ℂˣ) : ℂ) • GlobalTheory.TraceIncl.kern R i t h w v := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i t hθ hc hω hpt hio hD
  exact ⟨kern_fin R i t hio, kern_rat R i t hω hpt hio, kern_level R i t hθ hc hω hpt hio hD,
    kern_act R i t hθ hc hω hpt hio hD⟩

end GlobalTheory.TraceIncl
end
end

