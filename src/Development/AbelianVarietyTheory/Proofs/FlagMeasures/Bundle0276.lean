module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0269
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0039
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0076
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeFrameComponentLocalFrame
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.St.G.FrLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem prV_sigR (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] Ad F) :
    prV (E := E) v (sigR σ (Ad F) a) = sigR σ (v.adicCompletion F) (prV (E := E) v a) :=
  RingHom.congr_fun (Formalism.UG.P.afsplit_prV_comp_sigR σ v) a

theorem prV_OAd (v : HeightOneSpectrum (𝓞 F)) {a : E ⊗[F] Ad F} (ha : a ∈ OAd F E) :
    prV (E := E) v a ∈ intV E v :=
  ((GlobalTheory.St.G.IntAd.integral_adeles_properties F E).1 a).1 ha v

theorem prVec_add (v : HeightOneSpectrum (𝓞 F)) (x y : Fin n → E ⊗[F] Ad F) :
    prVec v (x + y) = prVec v x + prVec v y := by
  funext i; simp [prVec, map_add (f := _)]

theorem prVec_zero (v : HeightOneSpectrum (𝓞 F)) : prVec v (0 : Fin n → E ⊗[F] Ad F) = 0 := by
  funext i; simp [prVec]

theorem prVec_smul (v : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] Ad F) (x : Fin n → E ⊗[F] Ad F) :
    prVec v (a • x) = prV (E := E) v a • prVec v x := by
  funext i; simp [prVec, map_mul]

theorem prVec_span (v : HeightOneSpectrum (𝓞 F)) (S : Set (Fin n → E ⊗[F] Ad F))
    {x : Fin n → E ⊗[F] Ad F} (hx : x ∈ Submodule.span (OAd F E) S) :
    prVec v x ∈ Submodule.span (intV E v) (prVec v '' S) := by
  induction hx using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩
  | zero => rw [prVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [prVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    have h : prVec v (a • x) = (⟨prV (E := E) v a, prV_OAd v a.2⟩ : intV E v) • prVec v x :=
      prVec_smul v (a : E ⊗[F] Ad F) x
    rw [h]; exact Submodule.smul_mem _ _ hx

theorem prVec_hat (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E))
    {x : Fin n → E ⊗[F] Ad F} (hx : x ∈ hat F L) : prVec v x ∈ loc v L := by
  have h := prVec_span v _ hx
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
  exact ⟨l, hl, rfl⟩

theorem hR_prVec (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (x y : Fin n → E ⊗[F] Ad F) :
    hR σ J (v.adicCompletion F) (prVec v x) (prVec v y) = prV (E := E) v (hR σ J (Ad F) x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, hform, map_sum, map_mul, prV_sigR, prVec, Matrix.map_apply, Formalism.UG.P.afsplit_prV_inclE]

end GlobalTheory.St.G.FrLoc

open GlobalTheory.St.G.FrLoc in
theorem GlobalTheory.St.G.frame_component_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (g k : ℕ) (Fr : AdFrame σ J (hat F L) g k) (v : HeightOneSpectrum (𝓞 F)), prV (E := E) v Fr.eps * prV (E := E) v Fr.eps = prV (E := E) v Fr.eps ∧ prV (E := E) v Fr.eps * sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps) = 0 ∧ prV (E := E) v Fr.eps ∈ intV E v ∧ (∀ y ∈ loc v L, ∃ z ∈ loc v L, (1 - prV (E := E) v Fr.eps - sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps)) • y = (g : E ⊗[F] v.adicCompletion F) • z) ∧ (∀ i, prVec v (Fr.b i) ∈ loc v L) ∧ (∀ i, prVec v (Fr.bd i) ∈ loc v L) ∧ (∀ i, prVec v (Fr.b i) = prV (E := E) v Fr.eps • prVec v (Fr.b i)) ∧ (∀ i, prVec v (Fr.bd i) = sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps) • prVec v (Fr.bd i)) ∧ (∀ i j, ∃ t ∈ intV E v, hR σ J (v.adicCompletion F) (prVec v (Fr.bd i)) (prVec v (Fr.b j)) - (if i = j then prV (E := E) v Fr.eps else 0) = (g : E ⊗[F] v.adicCompletion F) * t) ∧ (∀ y ∈ loc v L, InModL (loc v L) g (Set.range (fun j => prVec v (Fr.b j)) ∪ Set.range (fun j => prVec v (Fr.bd j))) y) := by
  intro F E _ _ _ _ _ σ n J L g k Fr v
  refine ⟨?_, ?_, prV_OAd v Fr.eps_int, ?_, fun i => prVec_hat v L (Fr.b_mem i),
    fun i => prVec_hat v L (Fr.bd_mem i), ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, Fr.eps_idem]
  · rw [← prV_sigR, ← map_mul, Fr.eps_orth, map_zero]
  · intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      obtain ⟨z, hz, hzeq⟩ := Fr.eps_full (fun i => inclE (F := F) (Ad F) (l i))
        (Submodule.subset_span ⟨l, hl, rfl⟩)
      refine ⟨prVec v z, prVec_hat v L hz, ?_⟩
      have h := congrArg (prVec v) hzeq
      rw [prVec_smul, prVec_smul, map_sub, map_sub, map_one, prV_sigR, map_natCast] at h
      exact h
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨z₁, hz₁, e₁⟩ := hx
      obtain ⟨z₂, hz₂, e₂⟩ := hy
      exact ⟨z₁ + z₂, add_mem hz₁ hz₂, by rw [smul_add, smul_add, e₁, e₂]⟩
    | smul c x _ hx =>
      obtain ⟨z, hz, e⟩ := hx
      refine ⟨c • z, Submodule.smul_mem _ c hz, ?_⟩
      rw [Subring.smul_def, Subring.smul_def, smul_smul, mul_comm, ← smul_smul, e, smul_smul,
        smul_smul, mul_comm]
  · intro i
    have h := congrArg (prVec v) (Fr.b_eps i)
    rw [prVec_smul] at h
    exact h
  · intro i
    have h := congrArg (prVec v) (Fr.bd_eps i)
    rw [prVec_smul, prV_sigR] at h
    exact h
  · intro i j
    obtain ⟨t, ht, e⟩ := Fr.dual i j
    refine ⟨prV (E := E) v t, prV_OAd v ht, ?_⟩
    have h := congrArg (prV (E := E) v) e
    rw [map_sub, map_mul, map_natCast, ← hR_prVec, apply_ite (prV (E := E) v), map_zero] at h
    exact h
  · have hsub : prVec v '' (Set.range Fr.b ∪ Set.range Fr.bd) ⊆
        Set.range (fun j => prVec v (Fr.b j)) ∪ Set.range (fun j => prVec v (Fr.bd j)) := by
      rintro _ ⟨x, hx | hx, rfl⟩
      · obtain ⟨j, rfl⟩ := hx; exact Or.inl ⟨j, rfl⟩
      · obtain ⟨j, rfl⟩ := hx; exact Or.inr ⟨j, rfl⟩
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      obtain ⟨s, hs, z, hz, e⟩ := Fr.span (fun i => inclE (F := F) (Ad F) (l i))
        (Submodule.subset_span ⟨l, hl, rfl⟩)
      refine ⟨prVec v s, Submodule.span_mono hsub (prVec_span v _ hs), prVec v z, prVec_hat v L hz, ?_⟩
      have h := congrArg (prVec v) e
      rw [prVec_add, prVec_smul, map_natCast] at h
      exact h
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s₁, hs₁, z₁, hz₁, e₁⟩ := hx
      obtain ⟨s₂, hs₂, z₂, hz₂, e₂⟩ := hy
      refine ⟨s₁ + s₂, add_mem hs₁ hs₂, z₁ + z₂, add_mem hz₁ hz₂, ?_⟩
      rw [e₁, e₂, smul_add]; abel
    | smul c x _ hx =>
      obtain ⟨s, hs, z, hz, e⟩ := hx
      refine ⟨c • s, Submodule.smul_mem _ c hs, c • z, Submodule.smul_mem _ c hz, ?_⟩
      rw [e, smul_add, Subring.smul_def, Subring.smul_def, Subring.smul_def, smul_smul, smul_smul,
        mul_comm]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicInstanceExistsFundamentalDomain
section
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace
open Topology Filter

namespace GlobalTheory.FundExists

theorem exists_strict_domain {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (Γ : Subgroup G) [Countable Γ]
    (hfin : ∀ C : Set G, IsCompact C → (C ∩ Γ).Finite) :
    ∃ D : Set G, MeasurableSet D ∧ (∀ y, ∃ γ ∈ Γ, γ * y ∈ D) ∧
      ∀ γ ∈ Γ, ∀ y ∈ D, γ * y ∈ D → γ = 1 := by
  first
  | exact @_root_.GlobalTheory.MeasurableFundamentalDomain.exists_measurable_fundamental_domain
  | exact _root_.GlobalTheory.MeasurableFundamentalDomain.exists_measurable_fundamental_domain
  | (apply _root_.GlobalTheory.MeasurableFundamentalDomain.exists_measurable_fundamental_domain <;> assumption)
  | (intros; apply _root_.GlobalTheory.MeasurableFundamentalDomain.exists_measurable_fundamental_domain <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MeasurableFundamentalDomain.exists_measurable_fundamental_domain <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MeasurableFundamentalDomain.exists_measurable_fundamental_domain ..)

theorem exists_isFundDom : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf],
    ∃ fund, I.IsFundDom (I.muA μf) fund := by
  intro I μf _ _
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨Γ, hΓ, hc, hfin, -⟩ := GlobalTheory.RatDiscrete.rational_points I
  rw [← hΓ] at hfin
  obtain ⟨D, hD, hcov, hinj⟩ := exists_strict_domain Γ hfin
  refine ⟨D, hD, ?_, ?_⟩
  · rw [← hΓ]
    exact hcov
  · rw [← hΓ]
    intro γ hγ hne
    have : (fun y => γ * y) '' D ∩ D = ∅ := by
      refine Set.eq_empty_of_forall_notMem ?_
      rintro _ ⟨⟨y, hy, rfl⟩, hγy⟩
      exact hne (hinj γ hγ y hy hγy)
    rw [this, measure_empty]

end GlobalTheory.FundExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseFrameLatticeInvariantUnderAdaptedTranslate
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.TgTr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def Hom {T T' : E} (φ : S.V ≃ₗ[E] S.V) (A : LFlag S r T) (B : LFlag S r T') : Prop :=
  ∀ a : Fin (r + 1), φ (frame A a) - frame B a ∈ Xflag B a.val

theorem frame_castSucc {T : E} (A : LFlag S r T) (i : Fin r) : frame A i.castSucc = A.fl.e i := by
  simp [frame, FlagG.fvec, Fin.snoc_castSucc]

theorem frame_last {T : E} (A : LFlag S r T) : frame A (Fin.last r) = A.fl.z := by
  simp [frame, FlagG.fvec, Fin.snoc_last]

theorem xflag_mono {T : E} (A : LFlag S r T) {i j : ℕ} (h : i ≤ j) : Xflag A i ≤ Xflag A j := by
  exact Submodule.span_mono (Set.image_mono (fun k hk => lt_of_lt_of_le hk h))

theorem e_mem_xflag {T : E} (A : LFlag S r T) (i : Fin r) {j : ℕ} (h : i.1 < j) : A.fl.e i ∈ Xflag A j :=
  Submodule.subset_span ⟨i, h, rfl⟩

theorem Hom.map_mem {T T' : E} {φ : S.V ≃ₗ[E] S.V} {A : LFlag S r T} {B : LFlag S r T'} (h : Hom φ A B)
    (j : ℕ) {x : S.V} (hx : x ∈ Xflag A j) : φ x ∈ Xflag B j := by
  have hle : Xflag A j ≤ (Xflag B j).comap (φ : S.V →ₗ[E] S.V) := by
    apply Submodule.span_le.mpr
    rintro y ⟨i, hi, rfl⟩
    have h1 := h i.castSucc
    rw [frame_castSucc, frame_castSucc] at h1
    have h2 : φ (A.fl.e i) = (φ (A.fl.e i) - B.fl.e i) + B.fl.e i := by abel
    show φ (A.fl.e i) ∈ Xflag B j
    rw [h2]
    refine Submodule.add_mem _ ?_ (e_mem_xflag B i hi)
    exact xflag_mono B (le_of_lt hi) h1
  exact hle hx

theorem Hom.comp {T T' T'' : E} {φ ψ : S.V ≃ₗ[E] S.V} {A : LFlag S r T} {B : LFlag S r T'} {C : LFlag S r T''}
    (hφ : Hom φ B C) (hψ : Hom ψ A B) : Hom (φ * ψ) A C := by
  intro a
  have e1 : (φ * ψ) (frame A a) - frame C a = φ (ψ (frame A a) - frame B a) + (φ (frame B a) - frame C a) := by
    rw [LinearEquiv.mul_apply, map_sub]; abel
  rw [e1]
  exact Submodule.add_mem _ (hφ.map_mem _ (hψ a)) (hφ a)

theorem Hom.inv {T : E} {φ : S.V ≃ₗ[E] S.V} {A : LFlag S r T} (h : Hom φ A A) : Hom φ⁻¹ A A := by
  have hW : ∀ j : ℕ, ∀ x ∈ Xflag A j, φ⁻¹ x ∈ Xflag A j := by
    intro j x hx
    set W := Xflag A j
    have : FiniteDimensional E W := FiniteDimensional.span_of_finite E ((Set.toFinite _).image _)
    have hle : W.map (φ : S.V →ₗ[E] S.V) ≤ W := by
      rintro y ⟨w, hw, rfl⟩
      exact h.map_mem j hw
    have heq : W.map (φ : S.V →ₗ[E] S.V) = W :=
      Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq φ W)
    rw [← heq] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    have : φ⁻¹ (φ w) = w := by
      rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
    simpa [this] using hw
  intro a
  have e1 : φ⁻¹ (frame A a) - frame A a = -(φ⁻¹ (φ (frame A a) - frame A a)) := by
    have : φ⁻¹ (φ (frame A a)) = frame A a := by
      rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
    rw [map_sub, this]; abel
  rw [e1]
  exact Submodule.neg_mem _ (hW _ _ (h a))

theorem xflag_r {T : E} (A : LFlag S r T) : Xflag A r = Xsp A := by
  show Submodule.span E (A.fl.e '' {i | i.1 < r}) = Submodule.span E (Set.range A.fl.e)
  congr 1
  rw [← Set.image_univ]
  congr 1
  ext i; simp

theorem z_mem_orth {T : E} (A : LFlag S r T) : A.fl.z ∈ orth S (Xsp A) := by
  have hle : Xsp A ≤ LinearMap.ker (S.hT.flip A.fl.z) := by
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    show S.hT.flip A.fl.z (A.fl.e i) = 0
    rw [LinearMap.flip_apply]; exact A.fl.z_orth i
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  have := hle hx
  rw [LinearMap.mem_ker, LinearMap.flip_apply] at this
  exact this

theorem Hom.of_nlam {T : E} {Λ : Submodule (𝓞 E) S.V} {n : S.V ≃ₗ[E] S.V} {A : LFlag S r T}
    (h : n ∈ NLam Λ A) : Hom n A A := by
  obtain ⟨-, h2, h3⟩ := h
  intro a
  induction a using Fin.lastCases with
  | last =>
    rw [frame_last, Fin.val_last, xflag_r]
    exact h3 _ (z_mem_orth A)
  | cast i =>
    rw [frame_castSucc, Fin.val_castSucc]
    exact h2 i.1 _ (e_mem_xflag A i (Nat.lt_succ_self _))

theorem frame_mapLF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (A : LFlag S r T) (a : Fin (r + 1)) :
    frame (mapLF γ A) a = γ (frame A a) := by
  induction a using Fin.lastCases with
  | last => simp [mapLF, hγ, frame_last, mapFlag]
  | cast i => simp [mapLF, hγ, frame_castSucc, mapFlag]

theorem Hom.of_mapLF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (A : LFlag S r T) :
    Hom γ A (mapLF γ A) := by
  intro a
  rw [frame_mapLF hγ, sub_self]
  exact Submodule.zero_mem _

theorem gmap_mul (φ ψ : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap (φ * ψ) Λ = Formalism.HermitianLatticesTheory.gmap φ (Formalism.HermitianLatticesTheory.gmap ψ Λ) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨ψ y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem gmap_inv {φ : S.V ≃ₗ[E] S.V} {Λ : Submodule (𝓞 E) S.V} (h : Formalism.HermitianLatticesTheory.gmap φ Λ = Λ) :
    Formalism.HermitianLatticesTheory.gmap φ⁻¹ Λ = Λ := by
  conv_lhs => rw [← h]
  rw [← gmap_mul, inv_mul_cancel]
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

end GlobalTheory.Unfold.TgTr

namespace GlobalTheory.Unfold


open GlobalTheory.Unfold.TgTr in
theorem tg_translate : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (t₀ s : TauC Y u u') (Λ₀ : LV D) (a a' n n' : GV D), TG F F' t₀ Λ₀ → a ∈ Aut0 (lf D (X.Fu u)) t₀.lam → a' ∈ Aut0 (lf D (X.Fu u')) t₀.lam' → n ∈ NLam t₀.lam (lf D (X.Fu u)) → n' ∈ NLam t₀.lam' (lf D (X.Fu u')) → s.lam = t₀.lam → s.lin = n * (a * t₀.lin * a'⁻¹) * n' → TG F F' s Λ₀ := by
  intro D X Y u u' F F' t₀ s Λ₀ a a' n n' hTG ha ha' hn hn' hsl hsg
  obtain ⟨g, hgL, hgt, hΛ⟩ := hTG
  obtain ⟨⟨haI, haH⟩, haΛ⟩ := ha
  obtain ⟨⟨ha'I, ha'H⟩, -⟩ := ha'
  have hnH : Hom n _ _ := Hom.of_nlam hn
  have hn'H : Hom n' _ _ := Hom.of_nlam hn'
  have hnI : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hn.1.1
  have hnΛ : Formalism.HermitianLatticesTheory.gmap n t₀.lam = t₀.lam := hn.1.2
  have ht₀I : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have hsI : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  refine ⟨g * a⁻¹ * n⁻¹, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgL.1 (Subgroup.inv_mem _ haI)) (Subgroup.inv_mem _ hnI)
  · exact Hom.comp (Hom.comp (φ := g) hgL.2 (Hom.inv haH)) (Hom.inv hnH)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgL.1 (Subgroup.inv_mem _ haI)) (Subgroup.inv_mem _ hnI)
  · have hK : Hom (g * t₀.lin * a'⁻¹ * n') (lf D (X.Fu u')) F' :=
      Hom.comp (Hom.comp (Hom.comp (φ := g) hgt.2 (Hom.of_mapLF ht₀I _)) (Hom.inv ha'H)) hn'H
    have heq : g * a⁻¹ * n⁻¹ * s.lin = g * t₀.lin * a'⁻¹ * n' := by
      rw [hsg]; group
    intro c
    have hf : frame s.frame c = s.lin (frame (lf D (X.Fu u')) c) := frame_mapLF hsI _ c
    rw [hf, ← LinearEquiv.mul_apply, heq]
    exact hK c
  · rw [hsl, gmap_mul, gmap_mul, gmap_inv hnΛ, gmap_inv haΛ, hΛ]

end GlobalTheory.Unfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselLowestVectorLocalMassEqTransported
section
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PhiTranslate

variable {D : D7} {X : HidaSetting D}

theorem transp_mem (C : Choice X 1) (τ : D.what₂.Tau) {m : MatKR D.R.k D.R.rS}
    (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    Formalism.REAL.inUJ (X.B.I.ε (vOf X τ)) (C.Q τ * m * C.Qi τ) := by
  obtain ⟨-, h2, h3, -⟩ := C.isT τ
  have hm' : mᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hm
  unfold Formalism.REAL.inUJ
  calc (C.Q τ * m * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * m * C.Qi τ)
      = (C.Qi τ)ᴴ * (mᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * m) * C.Qi τ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.Qi τ := by rw [h3, hm']
    _ = (C.Q τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by rw [h2]; simp

theorem exists_uj {n : ℕ} {ε : Fin n → Bool} {M : Matrix (Fin n) (Fin n) ℂ} (hM : Formalism.REAL.inUJ ε M) :
    ∃ γ : Formalism.REAL.UJ ε, uMat γ = M := by
  have hM' : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε := hM
  have hl : (Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε) * M = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM', Formalism.REAL.Jm_mul_self]
  have hr : M * (Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε) = 1 := mul_eq_one_comm.1 hl
  exact ⟨⟨⟨M, _, hr, hl⟩, hM⟩, rfl⟩

theorem phiOf_eq (C : Choice X 1) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau) {m : MatKR D.R.k D.R.rS}
    (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    phiOf hB u τ m = wT C u τ (m * C.y τ) := by
  have hmy : m * C.y τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hm (C.y_mem τ)
  have hex : ∃ γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), uMat γ = C.Q τ * (m * C.y τ) * C.Qi τ :=
    exists_uj (transp_mem C τ hmy)
  unfold wT
  rw [dite_eq_left hex, (hB u τ).choose_spec.2 hex.choose, hex.choose_spec]
  unfold phiOf v0Of sigB bOf
  have hmul := (X.ds (vOf X τ)).2.2.1.1.2 _ (transp_mem C τ hm) _ (transp_mem C τ (C.y_mem τ))
  have e : C.Q τ * m * C.Qi τ * (C.Q τ * C.y τ * C.Qi τ) = C.Q τ * (m * C.y τ) * C.Qi τ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (C.Qi τ) (C.Q τ), (C.isT τ).1, Matrix.one_mul]
  rw [← ContinuousLinearMap.comp_apply, ← hmul, e]
  rfl

theorem bessel_lowest_vector_local_mass_eq_transported : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB →
    ∀ (u : D.what₂.Word) (τ : D.what₂.Tau), l2SG (C.nuS u τ) (phiOf hB u τ) = l2SG (C.nuS u τ) (wT C u τ) := by
  intro D X C hB hG u τ
  obtain ⟨hLF, hGW⟩ := hG
  obtain ⟨hW, -⟩ := hGW u τ
  obtain ⟨hc, -, hz, -, hTz, -, hGm, hWm, -, -, -, -, hq, -⟩ := hW
  obtain ⟨-, -, hSm, hcont, heq, -⟩ := hLF u τ
  have hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
    refine lt_of_lt_of_eq ?_ hTz.symm
    unfold Tr
    exact_mod_cast (D.mem u).A.T_prime.pos
  have hN0 : muNB D 1 ≠ 0 := by
    intro h0
    apply hSm.2.1
    show (((C.muW u τ).prod (muNB D 1)).map _ : Measure _) = 0
    rw [h0, Measure.prod_zero, Measure.map_zero]
  have hκ : kapN D 1 ≠ 0 := fun h => hN0 (by simp [muNB, haarLie, h])
  have hN : IsHaarOn (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) (muNB D 1) :=
    Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ hκ ENNReal.ofReal_ne_top
  obtain ⟨hGG, hGH⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular D.R.k D.R.rS
  obtain ⟨hGH1, hGH2⟩ := hGH _ hGm
  obtain ⟨hSG, hsub, hS1, hS2⟩ := GlobalTheory.muSof_isHaar _ _ _ _ _ hz hT hWm hN
  have hset : PI.QuotientSetting (BranchingSupport.GG D.R.k D.R.rS) (Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ))
      (muGB X (C.Q τ) (C.Qi τ) τ) (Formalism.FourierDecayAlt.ThreeDimData.muSof (C.muW u τ) (muNB D 1)) (C.nuS u τ) :=
    ⟨hGG, hSG, hsub, hGH1, hS1, hGH2, hS2, hq⟩
  obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hWm hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hGm.2.2.1 h0 h1 hq
  have hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ), ∀ x ∈ BranchingSupport.GG D.R.k D.R.rS,
      ‖wT C u τ (s * x)‖ = ‖wT C u τ x‖ := by
    rintro _ ⟨h', hh, m, hmN, rfl⟩ x hx
    rw [heq h' hh m hmN x hx, norm_smul,
      show ‖psiS D (zB X (C.Qi τ) u τ) m‖ = 1 from Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_norm _ _ _, one_mul]
    exact Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary hT hc h' hh _
  set A : Set (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) := {x | Matrix.of x ∈ BranchingSupport.GG D.R.k D.R.rS} with hA
  have hAm : MeasurableSet A := IsClosed.measurableSet (α := Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) hGG.1
  have hc' : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => ‖wT C u τ (Matrix.of x)‖₊) A := hcont.nnnorm
  have hm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => ‖wT C u τ (Matrix.of x)‖₊)
      (fun _ => 0)) :=
    hc'.measurable_piecewise continuousOn_const hAm
  have hval : ∀ x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS, Matrix.of x ∈ BranchingSupport.GG D.R.k D.R.rS →
      A.piecewise (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => ‖wT C u τ (Matrix.of x)‖₊) (fun _ => 0) x =
        ‖wT C u τ (Matrix.of x)‖₊ :=
    fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have key := GlobalTheory.QuotRightInv.quotInv _ _ _ _ _ _ hset _ (hm.coe_nnreal_ennreal.pow_const 2) (fun s hs x hx => by
    rw [hval x hx, hval (fun i j => (s * Matrix.of x) i j) (hGG.2.2.1 s (hsub hs) _ hx)]
    congr 2
    exact NNReal.eq (hinv s hs _ hx)) (C.y τ) (C.y_mem τ)
  unfold l2SG
  refine Eq.trans (lintegral_congr_ae (hae.mono fun x hx => ?_))
    (key.trans (lintegral_congr_ae (hae.mono fun x hx => ?_)))
  · simp only
    rw [hval (fun i j => (Matrix.of x * C.y τ) i j) (hGG.2.2.1 _ hx _ (C.y_mem τ)), phiOf_eq C hB u τ hx]
    rfl
  · simp only
    rw [hval x hx]

end GlobalTheory.PhiTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlueFrameCongruencesUnitriangularIntegralStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glue_frame_congruences_unitriangular_integral : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (r : ℕ) (Λ : Submodule (𝓞 E) S.V) (g : ℕ), 0 < g → ∀ (f f' : Fin (r + 1) → S.V), (∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a, f a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) → (∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, f' b - frameAct f ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ))) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, ModG S Λ g (f' b - frameAct f ξ b) := by
  first | exact @GlobalTheory.FrameGlue.glue | exact GlobalTheory.FrameGlue.glue | (intros; apply GlobalTheory.FrameGlue.glue <;> assumption)
end

