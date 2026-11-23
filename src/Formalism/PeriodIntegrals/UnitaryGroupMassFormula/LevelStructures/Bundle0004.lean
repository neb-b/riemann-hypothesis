module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatStab
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LocLevi

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ConjugateLevelCongruenceOf
section
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

def GlueHA : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (t : ∀ p : TypX X, HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J),
    ∃ h : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J,
      (∀ p : TypX X, haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) h = t p) ∧
      ∀ v, v ∉ typSet X.B.I.F (D.host.g 0) (D.host.g 1) →
        haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h = 1

def TensInj : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (x y : Af X.B.I.F ⊗[X.B.I.F] X.B.I.E),
    (∀ v : HeightOneSpectrum (𝓞 X.B.I.F), tensMap (E := X.B.I.E) (evalV X.B.I.F v) x =
      tensMap (E := X.B.I.E) (evalV X.B.I.F v) y) → x = y

def LevelCongruenceLocal : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.LevelSubgroupNormalized → ∀ κ : X.B.I.Gf,
    κ ∈ X.B.I.Kset → (∀ p : TypX X, ∃ κ' ∈ X.K2,
      haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb κ) =
        haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb κ')) → κ ∈ X.K2

theorem tens_lin {D : D7} (X : HidaSetting D) (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (h : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) (x : Fin X.B.I.n → X.B.I.E) (i : Fin X.B.I.n) :
    tensMap (E := X.B.I.E) (evalV X.B.I.F v) (lin (Af X.B.I.F) X.B.I.cm.sig X.B.I.J h
      (ratV (Af X.B.I.F) x) i) =
    lin (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h)
      (ratV (Fv X.B.I.F v) x) i := by
  change tensMap (E := X.B.I.E) (evalV X.B.I.F v) (∑ j, ((HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J h :
      GL (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) i j * inclR (Af X.B.I.F) (x j)) =
    ∑ j, ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
      (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h) : GL (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) i j * inclR (Fv X.B.I.F v) (x j)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, tensMap_inclR]
  rfl

theorem surjKH_of (hg : GlueHA) (hi : TensInj) : SurjKH := by
  intro D X w t htH htK
  classical
  obtain ⟨h, hT, hO⟩ := hg X t
  have hloc : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F),
      haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h ∈
        Hsub (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (frameOf X w) ∧
      haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h ∈
        Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v := by
    intro v
    by_cases hv : v ∈ typSet X.B.I.F (D.host.g 0) (D.host.g 1)
    · have e := hT ⟨v, hv⟩
      simp only at e
      rw [e]
      exact ⟨htH ⟨v, hv⟩, htK ⟨v, hv⟩⟩
    · rw [hO v hv]
      exact ⟨Subgroup.one_mem _, Subgroup.one_mem (Kloc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))⟩
  refine ⟨h, ?_, ?_, hT⟩
  · unfold Hsub
    rw [mem_stabT]
    intro b
    funext i
    apply hi X
    intro v
    rw [tens_lin X v h]
    have hv := (hloc v).1
    unfold Hsub at hv
    rw [mem_stabT] at hv
    rw [hv b]
    simp only [ratV, tensMap_inclR]
  · exact Subgroup.mem_iInf.2 fun v => (hloc v).2

theorem conjugate_level_congruence_of (hl : LevelCongruenceLocal) : ConjugateLevelLocalCongruence := by
  intro D X hb hK hL w h _ hKf hp
  have hc : finHA X hb (X.xu w) ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    finHA_mem_Kf X hb (X.xu w) (X.xu_K w)
  obtain ⟨κ, hκ⟩ := PI.MassDataKppVolLemmas.Bridge_tf_surjective X.B.I hb
    ((finHA X hb (X.xu w))⁻¹ * h * finHA X hb (X.xu w))
  have hκf : finHA X hb κ = (finHA X hb (X.xu w))⁻¹ * h * finHA X hb (X.xu w) := hκ
  have hκK : κ ∈ X.B.I.Kset := by
    refine (PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb κ).1 ?_
    change finHA X hb κ ∈ _
    rw [hκf]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hKf) hc
  have hmem : κ ∈ X.K2 := by
    refine hl X hb hK hL κ hκK (fun p => ?_)
    obtain ⟨y, ⟨_, ⟨k, hk, rfl⟩, rfl⟩, hy⟩ := hp p
    refine ⟨k, hk, ?_⟩
    rw [hκf]
    simp only [map_mul, map_inv] at hy ⊢
    rw [← hy]
    group
  exact ⟨finHA X hb κ, ⟨κ, hmem, rfl⟩, by rw [hκf]; group⟩

theorem global_product_of_local (hg : GlueHA) (hi : TensInj) (hl : LevelCongruenceLocal) : GlobProd :=
  globProd_of compH_holds compK_holds k2uGrp_holds (surjKH_of hg hi) (conjugate_level_congruence_of hl)

end MassDataLevelSSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.HaarIdxGlobOfFinProj
section
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge PI.MassDataKppVolLemmas
open Formalism.MainNotions.S (AutInst)
open scoped TensorProduct

def FinProjOpen : Prop :=
  ∀ I : AutInst, IsOpenMap (fun h : HAd I => (splitA I.cm.sig I.J h).2)

theorem finPart_inf_one (I : AutInst) (hb : AdBridgeIso I) (s : I.Ginf) :
    (splitA I.cm.sig I.J (toHA I hb (s, 1))).2 = 1 := by
  apply Bridge_HA_ext
  have hB : I.fmat 1 = ofHAFin I (toHA I hb (s, 1)) := (toHA_isBridge I hb (s, 1)).2
  have hm : ((HA.mat (Af I.F) I.cm.sig I.J ((splitA I.cm.sig I.J (toHA I hb (s, 1))).2) :
      GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) : Matrix (Fin I.n) (Fin I.n) _) =
      (ofHAFin I (toHA I hb (s, 1))).map (swapE I) := by
    ext i j
    simp only [ofHAFin, Matrix.map_apply]
    rw [← Bridge_tens_eq]
    rfl
  rw [hm, ← hB]
  have h1 : I.fmat 1 = 1 := rfl
  rw [h1, Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

theorem finPart_eq (I : AutInst) (hb : AdBridgeIso I) (s : I.Ginf) (x : I.Gf) :
    (splitA I.cm.sig I.J (toHA I hb (s, x))).2 = tf I hb x := by
  unfold tf
  rw [show ((s, x) : I.GA) = (s, 1) * (1, x) by ext <;> simp, map_mul, map_mul, Prod.snd_mul,
    finPart_inf_one I hb s, one_mul]

theorem one_mem_Kg (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  refine ⟨?_, fun y _ => ⟨0, zero_mem _, by simp [Formalism.MainNotions.S.AutInst.fmat]⟩⟩
  show _ ∈ Formalism.UG.stabGL I.Lf
  simpa using one_mem (Formalism.UG.stabGL I.Lf)

theorem level_subgroup_isOpen {D : D7} (X : HidaSetting D) (hL : X.LevelSubgroupNormalized) (hK : X.LevelSubgroupCharacter) :
    IsOpen (X.K2 : Set X.B.I.Gf) := by
  have hg1 : 1 ≤ X.B.g := by
    rw [X.g_eq]
    exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hKg : IsOpen (X.B.I.Kg X.B.g : Set X.B.I.Gf) := X.B.I.topf_open X.B.g hg1
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have ho : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (X.B.I.Kg X.B.g : Set X.B.I.Gf)) :=
    hKg.preimage (continuous_const.mul continuous_id)
  refine Filter.mem_of_superset (ho.mem_nhds (by simpa using one_mem_Kg X.B.I X.B.g)) ?_
  intro y hy
  have h2 := hK.2.1 x hx _ (hL.1 _ hy).1
  simpa using h2

theorem conjugate_level_isOpen (hP : FinProjOpen) {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)
    (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized) (w : D.what₂.Word) :
    IsOpen (K2u X hb w) := by
  set a := X.xu w
  have hU : IsOpen ((fun y => a * y * a⁻¹) '' X.K2) := by
    have e : (fun y => a * y * a⁻¹) '' X.K2 = (fun y => a⁻¹ * y * a) ⁻¹' X.K2 := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨k, hk, rfl⟩
        simpa [mul_assoc] using hk
      · intro hy
        exact ⟨a⁻¹ * y * a, hy, by group⟩
    rw [e]
    exact (level_subgroup_isOpen X hL hK).preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hW : IsOpen ((toHA X.B.I hb) '' (Set.univ ×ˢ ((fun y => a * y * a⁻¹) '' X.K2))) :=
    (toHA X.B.I hb).toHomeomorph.isOpenMap _ (isOpen_univ.prod hU)
  have e : K2u X hb w = (fun h : HAd X.B.I => (splitA X.B.I.cm.sig X.B.I.J h).2) ''
      ((toHA X.B.I hb) '' (Set.univ ×ˢ ((fun y => a * y * a⁻¹) '' X.K2))) := by
    have hom : ∀ k, tf X.B.I hb (a * k * a⁻¹) = finHA X hb a * finHA X hb k * (finHA X hb a)⁻¹ := by
      intro k
      show tfHom X.B.I hb (a * k * a⁻¹) = tfHom X.B.I hb a * tfHom X.B.I hb k * (tfHom X.B.I hb a)⁻¹
      rw [map_mul, map_mul, map_inv]
    ext h
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨toHA X.B.I hb (1, a * k * a⁻¹), ⟨(1, a * k * a⁻¹), ⟨trivial, k, hk, rfl⟩, rfl⟩, ?_⟩
      show (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (1, a * k * a⁻¹))).2 = _
      rw [finPart_eq, hom]
    · rintro ⟨_, ⟨⟨s, x⟩, ⟨-, k, hk, rfl⟩, rfl⟩, rfl⟩
      show (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (s, a * k * a⁻¹))).2 ∈ K2u X hb w
      rw [finPart_eq, hom]
      exact ⟨finHA X hb k, ⟨k, hk, rfl⟩, rfl⟩
  rw [e]
  exact hP X.B.I _ hW

theorem k2uOpenH_of (hP : FinProjOpen) : ConjugateLevelOpenUnitary := by
  unfold ConjugateLevelOpenUnitary
  intro D X hb hK _ hL w
  exact (conjugate_level_isOpen hP X hb hK hL w).preimage continuous_subtype_val

theorem haarIdxGlob_of_finProj (hP : FinProjOpen) : HaarIdxGlob :=
  haarIdxGlob_of (k2uOpenH_of hP)

def EvalVOpen : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)), IsOpenMap (haMap I.cm.sig I.J (evalV I.F v))

theorem k2vOpenS_of (hP : FinProjOpen) (hE : EvalVOpen) : ParabolicLevelOpenLocal := by
  intro D X hb hK _ hL w p
  exact ((hE X.B.I p.1) _ (conjugate_level_isOpen hP X hb hK hL w)).preimage continuous_subtype_val

theorem haarIdxLoc_of_open (hP : FinProjOpen) (hE : EvalVOpen) : HaarIdxLoc :=
  haarIdxLoc_of (k2vOpenS_of hP hE)

end MassDataLevelSSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.KSpTop
section
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem finiteDimensional_of_numberField (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : FiniteDimensional F E :=
  Module.Finite.of_restrictScalars_finite ℚ F E

theorem kSpCompact_holds : KSpCompact := by
  intro D X w p
  have := finiteDimensional_of_numberField X.B.I.F X.B.I.E
  exact (LatTop.isClosed_Ssub p.1 X.B.I.cm.sig X.B.I.J (frameOf X w)).isClosedEmbedding_subtypeVal.isCompact_preimage
    (LatTop.isCompact_Kv p.1 X.B.I.L X.B.I.L_span X.B.I.L_fg X.B.I.cm.sig X.B.I.J)

theorem kSpOpen_holds : KSpOpen := by
  intro D X w p
  have := finiteDimensional_of_numberField X.B.I.F X.B.I.E
  exact (LatTop.isOpen_Kv p.1 X.B.I.L X.B.I.L_span X.B.I.L_fg X.B.I.cm.sig X.B.I.J).preimage
    continuous_subtype_val

end MassDataLevelSSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LeviInt
section
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem hermForm_add_right_bis (x y z : Fin n → R ⊗[F] E) :
    hR R σ J x (y + z) = hR R σ J x y + hR R σ J x z := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hermForm_sub_right (x y z : Fin n → R ⊗[F] E) :
    hR R σ J x (y - z) = hR R σ J x y - hR R σ J x z := by
  simp only [hR, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hermForm_smul_right_alt (c : R ⊗[F] E) (x y : Fin n → R ⊗[F] E) :
    hR R σ J x (c • y) = c * hR R σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hermForm_sum_right_alt {ι : Type} (s : Finset ι) (d : ι → R ⊗[F] E) (v : ι → Fin n → R ⊗[F] E)
    (x : Fin n → R ⊗[F] E) : hR R σ J x (∑ i ∈ s, d i • v i) = ∑ i ∈ s, d i * hR R σ J x (v i) := by
  classical
  induction s using Finset.induction_on
  · simp only [Finset.sum_empty, hR, Formalism.UG.hform, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  · rename_i a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hermForm_add_right_bis, hermForm_smul_right_alt, ih]

theorem conjTensor_incl (a : E) : sigR R σ (inclR R a) = inclR R (σ a) := by
  simp [sigR, inclR]

theorem hermForm_rational_vectors (x y : Fin n → E) :
    hR R σ J (ratV (F := F) R x) (ratV (F := F) R y) = inclR R (hE σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [hR, hE, Formalism.UG.hform, ratV, JR, conjTensor_incl, map_sum, map_mul]

theorem mem_tensor_span_iff {r : ℕ} (Y : Fin r → Fin n → E) (y : Fin n → R ⊗[F] E)
    (hy : y ∈ spanR (F := F) R Y Set.univ) : ∃ d : Fin r → R ⊗[F] E, y = ∑ i, d i • ratV (F := F) R (Y i) := by
  simp only [spanR, Set.image_univ] at hy
  rw [Submodule.mem_span_range_iff_exists_fun] at hy
  obtain ⟨d, hd⟩ := hy
  exact ⟨d, hd.symm⟩

def WbR {r : ℕ} (P : Frame E n r) (w : Fin n → R ⊗[F] E) : Prop :=
  ∀ i, hR R σ J (ratV (F := F) R (P.e i)) w = 0 ∧ hR R σ J (ratV (F := F) R (P.f i)) w = 0

def WbSub {r : ℕ} (P : Frame E n r) : Submodule (R ⊗[F] E) (Fin n → R ⊗[F] E) where
  carrier := {w | WbR R σ J P w}
  add_mem' := by
    intro a b ha hb i
    rw [hermForm_add_right_bis, hermForm_add_right_bis, (ha i).1, (hb i).1, (ha i).2, (hb i).2]
    simp
  zero_mem' := by
    intro i
    have h := hermForm_smul_right_alt R σ J 0 (ratV (F := F) R (P.e i)) 0
    have h' := hermForm_smul_right_alt R σ J 0 (ratV (F := F) R (P.f i)) 0
    simp only [zero_smul, zero_mul] at h h'
    exact ⟨h, h'⟩
  smul_mem' := by
    intro c w hw i
    rw [hermForm_smul_right_alt, hermForm_smul_right_alt, (hw i).1, (hw i).2]
    simp

variable {R σ J}

theorem witt_decomposition_unique {r : ℕ} (P : Frame E n r) (hee : ∀ a b, hE σ J (P.e a) (P.e b) = 0)
    (hef : ∀ a b, hE σ J (P.e a) (P.f b) = if a = b then 1 else 0)
    (hfe : ∀ a b, hE σ J (P.f a) (P.e b) = if a = b then 1 else 0)
    {x a w b c : Fin n → R ⊗[F] E} (hx : x ∈ spanR (F := F) R P.e Set.univ)
    (ha : a ∈ spanR (F := F) R P.e Set.univ) (hc : c ∈ spanR (F := F) R P.f Set.univ)
    (hw : WbR R σ J P w) (hb : WbR R σ J P b) (h : x + w = a + b + c) : w = b := by
  classical
  have hax : a - x ∈ spanR (F := F) R P.e Set.univ := Submodule.sub_mem _ ha hx
  obtain ⟨g, hg⟩ := mem_tensor_span_iff (R := R) P.e (a - x) hax
  obtain ⟨d, hd⟩ := mem_tensor_span_iff (R := R) P.f c hc
  have hw' : w = a + b + c - x := by
    rw [← h]
    abel
  have hwb : w - b = (a - x) + c := by
    rw [hw']
    abel
  have hd0 : ∀ k, d k = 0 := by
    intro k
    have h1 : hR R σ J (ratV (F := F) R (P.e k)) (w - b) = 0 := by
      rw [hermForm_sub_right, (hw k).1, (hb k).1, sub_self]
    have h2 : hR R σ J (ratV (F := F) R (P.e k)) (a - x) = 0 := by
      rw [hg, hermForm_sum_right_alt]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hermForm_rational_vectors, hee, map_zero, mul_zero]
    have h3 : hR R σ J (ratV (F := F) R (P.e k)) c = d k := by
      rw [hd, hermForm_sum_right_alt, Finset.sum_eq_single k]
      · rw [hermForm_rational_vectors, hef, if_pos rfl, map_one, mul_one]
      · intro i _ hik
        rw [hermForm_rational_vectors, hef, if_neg (Ne.symm hik), map_zero, mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    rw [hwb, hermForm_add_right_bis, h2, h3, zero_add] at h1
    exact h1
  have hc0 : c = 0 := by
    rw [hd]
    exact Finset.sum_eq_zero fun i _ => by rw [hd0 i, zero_smul]
  have hg0 : ∀ k, g k = 0 := by
    intro k
    have h1 : hR R σ J (ratV (F := F) R (P.f k)) (w - b) = 0 := by
      rw [hermForm_sub_right, (hw k).2, (hb k).2, sub_self]
    have h3 : hR R σ J (ratV (F := F) R (P.f k)) (a - x) = g k := by
      rw [hg, hermForm_sum_right_alt, Finset.sum_eq_single k]
      · rw [hermForm_rational_vectors, hfe, if_pos rfl, map_one, mul_one]
      · intro i _ hik
        rw [hermForm_rational_vectors, hfe, if_neg (Ne.symm hik), map_zero, mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    rw [hwb, hc0, add_zero, h3] at h1
    exact h1
  have hax0 : a - x = 0 := by
    rw [hg]
    exact Finset.sum_eq_zero fun i _ => by rw [hg0 i, zero_smul]
  have hwb0 : w - b = 0 := by
    rw [hwb, hax0, hc0, add_zero]
  exact sub_eq_zero.mp hwb0

end Alg

end MassDataLevelSSteps
end
end

