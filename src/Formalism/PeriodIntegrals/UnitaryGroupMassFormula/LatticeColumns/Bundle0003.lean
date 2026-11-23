module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.IdxAbs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0008
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0020
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.ClassCount
section
noncomputable section

namespace PIW.MassDataColumns

open MeasureTheory
open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.PoincareInHH

theorem massCl_of_triv {G : Type} [Group G] (Γ K : Subgroup G)
    [Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G))]
    (h : ∀ x : G, Γ ⊓ K.map (MulAut.conj x).toMonoidHom = ⊥) :
    massCl Γ K = Nat.card (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) := by
  classical
  haveI := Fintype.ofFinite (DoubleCoset.Quotient (Γ : Set G) (K : Set G))
  unfold massCl
  simp only [h, Subgroup.card_bot, Nat.cast_one, inv_one]
  rw [finsum_eq_sum_of_fintype]
  simp [Nat.card_eq_fintype_card]

abbrev GamHA {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    Subgroup ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) :=
  (HFinIn (Af X.B.I.F) X.B.I.cm.sig X.B.I.J : Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)).subgroupOf
    (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))

abbrev ClsHA {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) : Type :=
  DoubleCoset.Quotient (G := ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))
    (GamHA X u : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))
    (unitaryLevelClosureSubgroup X hb u : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))

def ClassBijStep : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    AdBridgeGF X.B.I → X.LevelSubgroupNormalized →
    Nat.card (Formalism.L2.SG.ColsDim.Classes (PoincareSetting.iotaF X u) (PoincareSetting.Ku X u hK)) = Nat.card (ClsHA X hb u)

def HAStabTrivStep : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    AdBridgeGF X.B.I → X.LevelSubgroupNormalized →
    Formalism.L2.SG.ColsDim.StabTriv (PoincareSetting.iotaF X u) (PoincareSetting.Ku X u hK) →
    ∀ x : ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)),
      GamHA X u ⊓ (unitaryLevelClosureSubgroup X hb u).map (MulAut.conj x).toMonoidHom = ⊥

def UnfoldGenStep : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word),
    X.MeasTie hb →
    ∀ U : Subgroup ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)),
      IsOpen (U : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) →
      IsCompact (U : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) →
      MassFinite (GamHA X u) U →
      covol (X.measW u).μH = (X.muH u Set.univ).toReal * ((X.measW u).μHf (U : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))).toReal * massCl (GamHA X u) U ∧
        (X.muH u Set.univ).toReal * ((X.measW u).μHf (U : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))).toReal ≠ 0

theorem classCountStep_of (hB : ClassBijStep) (hS : HAStabTrivStep) (hU : UnfoldGenStep) (hG : IdxGroupStep)
    (hO : OpenCompactStep) : ClassCountStep' := by
  intro D X hb hK u hGF hMT hL hStab hFin
  obtain ⟨hset, hle⟩ := hG X hb hK u hMT hL
  obtain ⟨hopen, hcpt⟩ := hO X hb hK u hMT hL
  have hcard := hB X hb hK u hGF hL
  have htriv := hS X hb hK u hGF hL hStab
  have hneC : Nonempty (Formalism.L2.SG.ColsDim.Classes (PoincareSetting.iotaF X u) (PoincareSetting.Ku X u hK)) := by
    first
      | infer_instance
      | exact ⟨Quotient.mk _ 1⟩
      | exact ⟨DoubleCoset.mk _ _ 1⟩
  have hpos : 0 < Nat.card (ClsHA X hb u) := by
    rw [← hcard]
    exact Nat.card_pos
  haveI hfinH : Finite (ClsHA X hb u) := Nat.finite_of_card_ne_zero hpos.ne'
  haveI : IsTopologicalGroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := PIW.MassDataColumns.isTopGroup_HA _ _
  have hK2c : IsCompact (unitaryLevelClosureSubgroup X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :=
    hcpt.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hopen) hle
  have hMF : MassFinite (GamHA X u) (unitaryLevelClosureSubgroup X hb u) := by
    refine ⟨hfinH, fun x => ?_⟩
    rw [htriv x]
    infer_instance
  obtain ⟨hcov, hne⟩ := hU X hb u hMT (unitaryLevelClosureSubgroup X hb u) hopen hK2c hMF
  have hm : massCl (GamHA X u) (unitaryLevelClosureSubgroup X hb u) = Nat.card (ClsHA X hb u) :=
    massCl_of_triv _ _ htriv
  rw [hcov, hm, hset, hcard]
  rw [hset] at hne
  field_simp
  exact (div_self hne).symm

end PIW.MassDataColumns
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxProd
section
noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

variable {D : D7}

theorem piH_mem_KvH (X : HidaSetting D) (u : D.what₂.Word) (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (z : Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) (hz : z ∈ KHg X u) :
    piH X u v z ∈ KvH X u v := by
  have h : (z : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈
      Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := hz
  rw [Kf, Subgroup.mem_iInf] at h
  exact h v

def SurjH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ f : ∀ p : TypX X, KvH X u p.1,
      ∃ z ∈ KHg X u, ∀ p : TypX X, piH X u p.1 z = f p

def LocH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ z ∈ KHg X u,
      (∀ p : TypX X, ∃ w ∈ unitaryLevelClosureSubgroup X hb u, piH X u p.1 w = piH X u p.1 z) → z ∈ unitaryLevelClosureSubgroup X hb u

theorem idxProdH_of (hS : SurjH) (hL : LocH) : IdxProdH := by
  intro D X hb hK u hT hLv
  exact PI.MassDataKppVolLemmas.IdxAbs_relIndex (KHg X u) (unitaryLevelClosureSubgroup X hb u) (fun p : TypX X => piH X u p.1)
    (fun p : TypX X => KvH X u p.1) (fun p z hz => piH_mem_KvH X u p.1 z hz)
    (hS X hb hK u hT hLv) (hL X hb hK u hT hLv)

end PIW.MassDataColumns
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.LocRed
section
noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

variable {D : D7}

def KgH (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X) : Set (KvH X u p.1) :=
  {x | ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈
    Kgv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (gOf p) p.1}

def HLatGL (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ ψ : KvH X u p.1 →* GL (Fin D.R.k) (MassDataIdxSteps.Op X p), Function.Surjective ψ ∧
    ∀ x : KvH X u p.1, (∀ i j, ((ψ x : Matrix (Fin D.R.k) (Fin D.R.k) (MassDataIdxSteps.Op X p)) - 1) i j ∈
      Ideal.span {((gOf p : ℕ) : MassDataIdxSteps.Op X p)}) ↔ x ∈ KgH X u p

def HKerIn (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∀ x : KvH X u p.1, x ∈ KgH X u p → x ∈ (unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1)

def HImU (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∀ ρ : KvH X u p.1 →* GL (Fin D.R.k) (ZMod (gOf p)), Function.Surjective ρ →
    (∀ x, ρ x = 1 ↔ x ∈ KgH X u p) →
    Nat.card (((unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1)).map ρ) = ukC D.R.k (gOf p)

def LocRedParts : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ p : TypX X,
      MassDataIdxSteps.StResZ X p ∧ HLatGL X u p ∧ HKerIn X hb u p ∧ HImU X hb u p

private theorem isUnit_of_isUnit_map_of_surjective {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Nontrivial S]
    (f : R →+* S) (hf : Function.Surjective f) (r : R) (hr : IsUnit (f r)) : IsUnit r := by
  obtain ⟨v, hv⟩ := hr
  obtain ⟨y, hy⟩ := hf (↑v⁻¹ : S)
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (r * y) with h | h
  · exact isUnit_of_mul_isUnit_left h
  · exfalso
    have h2 := h.map f
    rw [map_sub, map_one, map_mul, ← hv, hy, Units.mul_inv, sub_self] at h2
    exact not_isUnit_zero h2

private theorem generalLinearGroup_map_surjective_of_surjective {R S m : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Fintype m]
    [DecidableEq m] (f : R →+* S) (hf : Function.Surjective f) :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := m) f) := by
  intro A
  rcases subsingleton_or_nontrivial S with hS | hS
  · exact ⟨1, Units.ext (Matrix.ext fun i j => Subsingleton.elim _ _)⟩
  · have hf' := hf
    choose g hg using hf'
    let M : Matrix m m R := fun i j => g ((A : Matrix m m S) i j)
    have hM : f.mapMatrix M = (A : Matrix m m S) := by
      ext i j
      exact hg _
    have hdet : IsUnit M.det := by
      apply isUnit_of_isUnit_map_of_surjective f hf
      rw [RingHom.map_det, hM]
      exact (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit
    refine ⟨((Matrix.isUnit_iff_isUnit_det M).mpr hdet).unit, ?_⟩
    apply Units.ext
    change f.mapMatrix (((Matrix.isUnit_iff_isUnit_det M).mpr hdet).unit : Matrix m m R) = _
    rw [IsUnit.unit_spec, hM]

theorem locRedH_of (h : LocRedParts) : LocRedH := by
  intro D X hb hK u hm hl p
  obtain ⟨⟨π, hπs, hπk⟩, ⟨ψ, hψs, hψ⟩, hker, himu⟩ := h X hb hK u hm hl p
  let ρ : KvH X u p.1 →* GL (Fin D.R.k) (ZMod (gOf p)) :=
    (Matrix.GeneralLinearGroup.map π).comp ψ
  have hco : ∀ (x : KvH X u p.1) (i j : Fin D.R.k),
      ((ρ x : GL (Fin D.R.k) (ZMod (gOf p))) : Matrix (Fin D.R.k) (Fin D.R.k) (ZMod (gOf p))) i j =
        π (((ψ x : GL (Fin D.R.k) (MassDataIdxSteps.Op X p)) :
          Matrix (Fin D.R.k) (Fin D.R.k) (MassDataIdxSteps.Op X p)) i j) :=
    fun _ _ _ => rfl
  have hentry : ∀ (x : KvH X u p.1) (i j : Fin D.R.k),
      (((ψ x : GL (Fin D.R.k) (MassDataIdxSteps.Op X p)) :
          Matrix (Fin D.R.k) (Fin D.R.k) (MassDataIdxSteps.Op X p)) - 1) i j ∈
          Ideal.span {((gOf p : ℕ) : MassDataIdxSteps.Op X p)} ↔
        ((ρ x : GL (Fin D.R.k) (ZMod (gOf p))) : Matrix (Fin D.R.k) (Fin D.R.k) (ZMod (gOf p))) i j =
          (1 : Matrix (Fin D.R.k) (Fin D.R.k) (ZMod (gOf p))) i j := by
    intro x i j
    rw [← hπk, RingHom.mem_ker, hco, Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.one_apply,
      Matrix.one_apply]
    split_ifs <;> simp
  have hρ1 : ∀ x, ρ x = 1 ↔ x ∈ KgH X u p := by
    intro x
    rw [← hψ x]
    constructor
    · intro hx i j
      exact (hentry x i j).2 (by rw [hx, Units.val_one])
    · intro hx
      apply Units.ext
      apply Matrix.ext
      intro i j
      rw [Units.val_one]
      exact (hentry x i j).1 (hx i j)
  have hρs : Function.Surjective ρ := (generalLinearGroup_map_surjective_of_surjective π hπs).comp hψs
  exact ⟨ρ, hρs, fun x hx => hker x ((hρ1 x).1 (MonoidHom.mem_ker.mp hx)), himu ρ hρs hρ1⟩

end PIW.MassDataColumns
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.OpenCompact
section
noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

def FinHAHomeo : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (hb : AdBridgeIso I), ∃ e : I.Gf ≃ₜ* HA (Af I.F) I.cm.sig I.J,
    ∀ x, e x = (splitA I.cm.sig I.J (toHA I hb (1, x))).2

def LevelOpenCompact : Prop := ∀ {D : D7} (X : HidaSetting D), IsOpen X.K2 ∧ IsCompact X.K2

def KsetCompactAll : Prop := ∀ I : Formalism.MainNotions.S.AutInst, IsCompact I.Kset

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem isClosed_stabT_Af {a : ℕ} (X0 : Fin a → Fin n → E) :
    IsClosed ((stabT (Af F) σ J X0 : Subgroup (HA (Af F) σ J)) : Set (HA (Af F) σ J)) := by
  have : IsTopologicalRing (Af F ⊗[F] E) := PI.AdicCompletionValuation.isTopologicalRing_tens (F := F) (E := E) (Af F)
  have : T2Space (Af F ⊗[F] E) := PI.AdicCompletionValuation.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (Af F)
  have hcont : Continuous fun g : HA (Af F) σ J => g • ratTup (F := F) (Af F) X0 := by
    show Continuous fun g : HA (Af F) σ J => actTup (Af F) (HA.mat (Af F) σ J g) (ratTup (F := F) (Af F) X0)
    unfold actTup HA.mat
    refine continuous_pi fun b => Continuous.matrix_mulVec ?_ continuous_const
    exact Units.continuous_val.comp
      (continuous_subtype_val : Continuous fun g : HR (Af F) σ J => (g : GL (Fin n) (Af F ⊗[F] E)))
  have : ((stabT (Af F) σ J X0 : Subgroup (HA (Af F) σ J)) : Set (HA (Af F) σ J)) =
      {g | g • ratTup (F := F) (Af F) X0 = ratTup (F := F) (Af F) X0} := by
    ext g
    exact MulAction.mem_stabilizer_iff
  rw [this]
  exact isClosed_eq hcont continuous_const

end Gen

theorem finHA_mem_Kf_iff {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (x : X.B.I.Gf) :
    finHA X hb x ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔ x ∈ X.B.I.Kset := by
  have hK := adelic_compact_finite_places X.B.I (toHA X.B.I hb (1, x))
  have hbr : X.B.I.fmat x = ofHAFin X.B.I (toHA X.B.I hb (1, x)) := (toHA_isBridge X.B.I hb (1, x)).2
  rw [← hbr] at hK
  rw [Kf, Subgroup.mem_iInf]
  constructor
  · intro h
    exact hK.2 h
  · intro h
    exact hK.1 h

theorem kf_eq_image {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)
    (hs : Function.Surjective (finHA X hb)) :
    (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) = finHA X hb '' X.B.I.Kset := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, rfl⟩ := hs z
    exact ⟨x, (finHA_mem_Kf_iff X hb x).1 hz, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (finHA_mem_Kf_iff X hb x).2 hx

theorem openCompactStep_of (hE : FinHAHomeo) (hK2 : LevelOpenCompact) (hKc : KsetCompactAll) :
    OpenCompactStep := by
  intro D X hb hK u _hT _hL
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := isTopGroup_HA (F := X.B.I.F) (E := X.B.I.E) X.B.I.cm.sig X.B.I.J
  obtain ⟨e, he⟩ := hE X.B.I hb
  have hfe : (finHA X hb : X.B.I.Gf → HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) = e := by
    funext x
    exact (he x).symm
  constructor
  ·
    have hset : (unitaryLevelClosureSubgroup X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) =
        Subtype.val ⁻¹' K2u X hb u := by
      unfold unitaryLevelClosureSubgroup
      have : (Subtype.val ⁻¹' K2u X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) =
          (unitaryLevelIntersection X hb hK u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) := rfl
      rw [this, Subgroup.closure_eq]
    rw [hset]
    refine IsOpen.preimage continuous_subtype_val ?_
    have h1 : IsOpen (levelUnitary X hb) := by
      unfold levelUnitary
      rw [hfe]
      exact e.toHomeomorph.isOpenMap _ (hK2 X).1
    set a := finHA X hb (X.xu u)
    have hc : K2u X hb u = ((Homeomorph.mulLeft a).trans (Homeomorph.mulRight a⁻¹)) '' levelUnitary X hb := rfl
    rw [hc]
    exact ((Homeomorph.mulLeft a).trans (Homeomorph.mulRight a⁻¹)).isOpenMap _ h1
  ·
    have hsurj : Function.Surjective (finHA X hb) := by
      rw [hfe]
      exact e.surjective
    have hKf : IsCompact (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
        Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) := by
      rw [kf_eq_image X hb hsurj, hfe]
      exact (hKc X.B.I).image e.continuous
    have hH : IsClosed ((Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) :
        Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :=
      isClosed_stabT_Af X.B.I.cm.sig X.B.I.J (tupH (frameOf X u))
    rw [Subtype.isCompact_iff]
    have : ((↑) : Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) → HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ''
        (KHg X u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) =
        (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) ∩
          (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
            Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) := by
      ext z
      simp only [Set.mem_image, SetLike.mem_coe, Set.mem_inter_iff, KHg, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨z, h1⟩, h2, rfl⟩
    rw [this]
    exact hKf.inter_left hH

end PIW.MassDataColumns
end
end

