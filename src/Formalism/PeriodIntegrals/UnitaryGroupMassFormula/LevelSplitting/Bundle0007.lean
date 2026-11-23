module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.UnitaryGroupSecondCountableT2
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.HeisenbergCocycleMemCentre
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LeviInfUnipotentEqOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCAsmV

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.CoordinateHomeomorphism
section
noncomputable section

namespace PI.LevelKSplit.W.NC

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Q : Type} [AddCommGroup Q] [TopologicalSpace Q] [ContinuousAdd Q]

structure CoordHyp (N A N1 Z : Subgroup G) (Lev : G → G) (sH : Q → G) (yQ : N1 → Q) : Prop where
  hAN : A ≤ N
  coordinate_level_le : N1 ≤ N
  hZN1 : Z ≤ N1
  cLev : Continuous Lev
  csH : Continuous sH
  cyQ : Continuous yQ
  lev_mem : ∀ n ∈ N, Lev n ∈ A
  lev_rest : ∀ n ∈ N, (Lev n)⁻¹ * n ∈ N1
  triv : ∀ u ∈ A, u ∈ N1 → u = 1
  norm1 : ∀ n ∈ N, ∀ m ∈ N1, n * m * n⁻¹ ∈ N1
  sH_mem : ∀ y, sH y ∈ N1
  dec : ∀ m : N1, (sH (yQ m))⁻¹ * (m : G) ∈ Z
  yQ_sH : ∀ y z (hz : z ∈ Z), yQ ⟨sH y * z, N1.mul_mem (sH_mem y) (hZN1 hz)⟩ = y
  cent : ∀ z ∈ Z, ∀ m ∈ N1, z * m = m * z
  mul : ∀ y y', sH y * sH y' * (sH (y + y'))⁻¹ ∈ Z

variable {N A N1 Z : Subgroup G} {Lev : G → G} {sH : Q → G} {yQ : N1 → Q}

theorem lev_eq (H : CoordHyp N A N1 Z Lev sH yQ) (u : A) (w : G) (hw : w ∈ N1) :
    Lev ((u : G) * w) = u := by
  have hg : (u : G) * w ∈ N := N.mul_mem (H.hAN u.2) (H.coordinate_level_le hw)
  set v := Lev ((u : G) * w) with hv
  have h1 : v⁻¹ * (u : G) ∈ N1 := by
    have : v⁻¹ * (u : G) = (v⁻¹ * ((u : G) * w)) * w⁻¹ := by group
    rw [this]
    exact N1.mul_mem (H.lev_rest _ hg) (N1.inv_mem hw)
  have h2 : v⁻¹ * (u : G) ∈ A := A.mul_mem (A.inv_mem (H.lev_mem _ hg)) u.2
  have h3 := H.triv _ h2 h1
  have : (u : G) = v := by
    calc (u : G) = v * (v⁻¹ * u) := by group
      _ = v := by rw [h3, mul_one]
  exact this.symm

def cfun (H : CoordHyp N A N1 Z Lev sH yQ) (p : A × (Q × Z)) : N :=
  ⟨(p.1 : G) * sH p.2.1 * (p.2.2 : G),
    N.mul_mem (N.mul_mem (H.hAN p.1.2) (H.coordinate_level_le (H.sH_mem _))) (H.coordinate_level_le (H.hZN1 p.2.2.2))⟩

def cm (H : CoordHyp N A N1 Z Lev sH yQ) (n : N) : N1 :=
  ⟨(Lev n)⁻¹ * (n : G), H.lev_rest n n.2⟩

def cinv (H : CoordHyp N A N1 Z Lev sH yQ) (n : N) : A × (Q × Z) :=
  (⟨Lev n, H.lev_mem n n.2⟩, yQ (cm H n), ⟨(sH (yQ (cm H n)))⁻¹ * (cm H n : G), H.dec _⟩)

theorem cinv_cfun (H : CoordHyp N A N1 Z Lev sH yQ) (p : A × (Q × Z)) :
    cinv H (cfun H p) = p := by
  obtain ⟨u, y, z⟩ := p
  have hw : sH y * (z : G) ∈ N1 := N1.mul_mem (H.sH_mem y) (H.hZN1 z.2)
  have hL : Lev ((u : G) * sH y * (z : G)) = u := by
    rw [mul_assoc]; exact lev_eq H u _ hw
  have hm : cm H (cfun H (u, y, z)) = ⟨sH y * (z : G), hw⟩ := by
    apply Subtype.ext
    simp only [cm, cfun]
    rw [hL]; group
  have hy : yQ (cm H (cfun H (u, y, z))) = y := by
    rw [hm]; exact H.yQ_sH y z z.2
  refine Prod.ext (Subtype.ext ?_) (Prod.ext hy (Subtype.ext ?_))
  · simp only [cinv, cfun]; exact hL
  · simp only [cinv]
    rw [hy, hm]
    group

theorem cfun_cinv (H : CoordHyp N A N1 Z Lev sH yQ) (n : N) : cfun H (cinv H n) = n := by
  apply Subtype.ext
  simp only [cfun, cinv, cm]
  group

theorem continuous_cm (H : CoordHyp N A N1 Z Lev sH yQ) : Continuous (cm H) :=
  Continuous.subtype_mk ((H.cLev.comp continuous_subtype_val).inv.mul continuous_subtype_val) _

def cHomeo (H : CoordHyp N A N1 Z Lev sH yQ) : (A × (Q × Z)) ≃ₜ N where
  toFun := cfun H
  invFun := cinv H
  left_inv := cinv_cfun H
  right_inv := cfun_cinv H
  continuous_toFun := Continuous.subtype_mk
    (((continuous_subtype_val.comp continuous_fst).mul
      (H.csH.comp (continuous_fst.comp continuous_snd))).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))) _
  continuous_invFun := by
    have h1 := continuous_cm H
    refine Continuous.prodMk (Continuous.subtype_mk (H.cLev.comp continuous_subtype_val) _)
      (Continuous.prodMk (H.cyQ.comp h1) (Continuous.subtype_mk ?_ _))
    exact (H.csH.comp (H.cyQ.comp h1)).inv.mul (continuous_subtype_val.comp h1)

theorem cHomeo_apply (H : CoordHyp N A N1 Z Lev sH yQ) (p : A × (Q × Z)) :
    ((cHomeo H p : N) : G) = (p.1 : G) * sH p.2.1 * (p.2.2 : G) := rfl

theorem coord_skew (H : CoordHyp N A N1 Z Lev sH yQ) (n0 : N) :
    ∃ (a0 : A) (t : A → Q) (c : A × Q → Z), Continuous t ∧ Continuous c ∧
      ∀ u y z, n0 * cHomeo H (u, y, z) = cHomeo H (a0 * u, y + t u, c (u, y) * z) := by
  set a0 : A := ⟨Lev n0, H.lev_mem n0 n0.2⟩
  set n1 : G := (Lev n0)⁻¹ * (n0 : G) with hn1
  have hn1m : n1 ∈ N1 := H.lev_rest n0 n0.2
  have hmf : ∀ u : A, (u : G)⁻¹ * n1 * u ∈ N1 := fun u => by
    have := H.norm1 ((u : G)⁻¹) (N.inv_mem (H.hAN u.2)) n1 hn1m
    simpa using this
  let mf : A → N1 := fun u => ⟨(u : G)⁻¹ * n1 * u, hmf u⟩
  have cmf : Continuous mf := Continuous.subtype_mk
    ((continuous_subtype_val.inv.mul continuous_const).mul continuous_subtype_val) _
  let t : A → Q := fun u => yQ (mf u)
  have ct : Continuous t := H.cyQ.comp cmf
  let zm : A → G := fun u => (sH (t u))⁻¹ * (mf u : G)
  have hzm : ∀ u, zm u ∈ Z := fun u => H.dec (mf u)
  let k : A × Q → G := fun p => sH (t p.1) * sH p.2 * (sH (t p.1 + p.2))⁻¹
  have hk : ∀ p, k p ∈ Z := fun p => H.mul _ _
  let c : A × Q → Z := fun p => ⟨k p * zm p.1, Z.mul_mem (hk p) (hzm p.1)⟩
  have cc : Continuous c := by
    refine Continuous.subtype_mk ?_ _
    have ct1 : Continuous (fun p : A × Q => t p.1) := ct.comp continuous_fst
    refine (((H.csH.comp ct1).mul (H.csH.comp continuous_snd)).mul
      (H.csH.comp (ct1.add continuous_snd)).inv).mul ?_
    exact (H.csH.comp ct1).inv.mul (continuous_subtype_val.comp (cmf.comp continuous_fst))
  refine ⟨a0, t, c, ct, cc, fun u y z => ?_⟩
  apply Subtype.ext
  show (n0 : G) * ((u : G) * sH y * (z : G)) = (Lev n0 * u) * sH (y + t u) * (k (u, y) * zm u * z)
  have e2 : (mf u : G) = sH (t u) * zm u := by
    show (mf u : G) = sH (t u) * ((sH (t u))⁻¹ * (mf u : G)); group
  have e3 : zm u * sH y = sH y * zm u := H.cent _ (hzm u) _ (H.sH_mem y)
  have e4 : sH (t u) * sH y = sH (t u + y) * k (u, y) := by
    have h := H.cent _ (hk (u, y)) _ (H.sH_mem (t u + y))
    calc sH (t u) * sH y = k (u, y) * sH (t u + y) := by show _ = sH (t u) * sH y * (sH (t u + y))⁻¹ * sH (t u + y); group
      _ = sH (t u + y) * k (u, y) := h
  have e1 : (n0 : G) * ((u : G) * sH y * (z : G)) = Lev n0 * u * (mf u : G) * sH y * z := by
    show _ = Lev n0 * u * ((u : G)⁻¹ * ((Lev n0)⁻¹ * (n0 : G)) * u) * sH y * z
    group
  rw [e1, e2, add_comm y (t u)]
  calc Lev n0 * (u : G) * (sH (t u) * zm u) * sH y * (z : G)
      = Lev n0 * u * sH (t u) * (zm u * sH y) * z := by group
    _ = Lev n0 * u * sH (t u) * (sH y * zm u) * z := by rw [e3]
    _ = Lev n0 * u * (sH (t u) * sH y) * zm u * z := by group
    _ = Lev n0 * u * (sH (t u + y) * k (u, y)) * zm u * z := by rw [e4]
    _ = (Lev n0 * u) * sH (t u + y) * (k (u, y) * zm u * z) := by group

end Gen

end PI.LevelKSplit.W.NC
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.HeisenbergParabolicAll
section
noncomputable section

namespace PI.LevelKSplit.W.NCH

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.VolSemiDirect.W NumberField IsDedekindDomain
open scoped TensorProduct

theorem heisenberg_parabolic (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    PI.LevelKSplit.W.NC.HeisP F E σ M J := by
  intro hJ hσσ r P T hP
  have H : (datR (Af F) σ J P T).Hyp := datR_hyp (R := Af F) hσσ hJ hP
  have hh : Half (datR (Af F) σ J P T) (algebraMap F (Af F ⊗[F] E) (1 / 2)) := by
    refine ⟨?_, ?_⟩
    · rw [← map_add (f := _), add_halves, map_one]
    · show (Algebra.TensorProduct.map (AlgHom.id F (Af F)) σ) (algebraMap F (Af F ⊗[F] E) (1 / 2)) =
        algebraMap F (Af F ⊗[F] E) (1 / 2)
      exact AlgHom.commutes _ _
  have hcy : Continuous fun y : Fin r → PI.LevelKSplit.W.NC.Wp (Af F) σ J P =>
      fun a => (y a : Fin M → Af F ⊗[F] E) :=
    continuous_pi fun a => continuous_subtype_val.comp (continuous_apply a)
  refine ⟨fun y => sHG hJ H hh (y := fun a => (y a : Fin M → Af F ⊗[F] E)) (fun a => (y a).2),
    ?_, continuous_yH P, fun y => sHG_mem hJ H hh _, fun g hg => ?_, fun y z hz a => ?_,
    centre_le_unipotent_radical hJ H hh, fun z hz g hg => Z_comm hJ H hh hz hg, fun y y' => ?_,
    fun g hg z hz => N_norm_Z hJ H hh hg hz, fun g hg y => ?_, fun g hg z hz => H_comm_Z hJ H hh hg hz⟩
  · exact Md.continuous_into_HA hJ (continuous_sLmat P T _ hcy)
  · exact ⟨fun a => ⟨_, isWp_yH hJ H hh g a⟩, fun a => rfl, inv_mul_mem_Z hJ H hh hg⟩
  · exact (yH_mul_Z hJ H hh (sHG_mem hJ H hh _) hz a).trans (yH_sHG hJ H hh _ a)
  · exact heisenberg_cocycle_mem_centre hJ H hh (y := fun a => (y a : Fin M → Af F ⊗[F] E))
      (y' := fun a => (y' a : Fin M → Af F ⊗[F] E)) (fun a => (y a).2) (fun a => (y' a).2)
      (fun a => ((y + y') a).2)
  · exact ⟨fun a => ⟨lin (Af F) σ J g (y a), H_isWp hJ H hh hg (y a).2⟩, fun a => rfl,
      H_conj_sHG hJ H hh hg _ _⟩

theorem heisenberg_parabolic_all : PI.LevelKSplit.W.NC.HeisPAll := by
  intro F E _ _ _ _ _ σ hσ M J _
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  exact heisenberg_parabolic F E σ M J

end PI.LevelKSplit.W.NCH
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.IsClosedAsub
section
noncomputable section

namespace PI.LevelKSplit.W.NCL

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r}

theorem mem_Asub {g : HA R σ J} : g ∈ Asub R σ J P ↔ (g ∈ Nsub R σ J P ∧
    (∀ w ∈ PI.LevelKSplit.W.NC.Wp R σ J P, lin R σ J g w = w) ∧
    (∀ b, lin R σ J g (ratV (F := F) R (P.f b)) ∈ spanR (F := F) R P.f Set.univ) ∧
    (∀ b, lin R σ J g⁻¹ (ratV (F := F) R (P.f b)) ∈ spanR (F := F) R P.f Set.univ)) := Iff.rfl

theorem Asub_le : Asub R σ J P ≤ Nsub R σ J P := fun _ hg => (mem_Asub.1 hg).1

end Gen

section Af

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ}

theorem isClosed_Asub (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x) (P : Frame E M r) (T : F)
    (hP : P.IsStd σ J T) : IsClosed (Asub (Af F) σ J P : Set (HA (Af F) σ J)) := by
  have hD : ∀ a a', hE σ J (P.e a') (P.f a) = if a = a' then 1 else 0 := fun a a' => by
    rw [hP.2.2.1 a' a]
    by_cases h : a = a'
    · subst h; simp
    · simp [h, Ne.symm h]
  have hF : IsClosed (spanR (F := F) (Af F) P.f Set.univ : Set (Fin M → Af F ⊗[F] E)) :=
    PI.LevelKSplit.W.ExC.isClosed_spanR P.f P.e hD Set.univ
  have e : (Asub (Af F) σ J P : Set (HA (Af F) σ J)) =
      (Nsub (Af F) σ J P : Set (HA (Af F) σ J)) ∩
        ((⋂ w ∈ PI.LevelKSplit.W.NC.Wp (Af F) σ J P, {g : HA (Af F) σ J | lin (Af F) σ J g w = w}) ∩
        ((⋂ b, {g : HA (Af F) σ J | lin (Af F) σ J g (ratV (F := F) (Af F) (P.f b)) ∈
            spanR (F := F) (Af F) P.f Set.univ}) ∩
          (⋂ b, {g : HA (Af F) σ J | lin (Af F) σ J g⁻¹ (ratV (F := F) (Af F) (P.f b)) ∈
            spanR (F := F) (Af F) P.f Set.univ}))) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact mem_Asub
  rw [e]
  refine (PI.LevelKSplit.W.ExC.closed_SNH hJ hinv P T hP).2.1.inter
    ((isClosed_biInter fun w _ => ?_).inter ((isClosed_iInter fun b => ?_).inter
      (isClosed_iInter fun b => ?_)))
  · exact isClosed_eq (Md.continuous_linear_action (Af F) σ J continuous_id continuous_const) continuous_const
  · exact hF.preimage (Md.continuous_linear_action (Af F) σ J continuous_id continuous_const)
  · exact hF.preimage (Md.continuous_linear_action (Af F) σ J continuous_inv continuous_const)

end Af

end PI.LevelKSplit.W.NCL
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCAsmM
section
noncomputable section

namespace PI.LevelKSplit.W.NCA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open PI.LevelKSplit PI.LevelKSplit.W.NC PI.LevelKSplit.W.SemiA PI.VolSemiDirect.W
open scoped TensorProduct

theorem conjInv_of_one {X : Type} [Group X] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (N H : Subgroup X) (hN : LCSC N)
    (hex : ∀ h ∈ H, ∃ μ0 : Measure N, μ0.IsHaarMeasure ∧ ∀ f : X → ENNReal, Measurable f →
      ∫⁻ n, f (h * (n : X) * h⁻¹) ∂μ0 = ∫⁻ n, f (n : X) ∂μ0) : ConjInv N H := by
  obtain ⟨hlc, hsc, ht2, htg⟩ := hN
  intro μN hμN h hh f hf
  obtain ⟨μ0, hμ0, hinv⟩ := hex h hh
  rw [Measure.isMulLeftInvariant_eq_smul μN μ0, lintegral_smul_measure, lintegral_smul_measure,
    hinv f hf]

section Af

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem conjNH_of (hC : NCoord F E σ M J) (hV : PI.LevelKSplit.W.CD.ModV F E σ M J) :
    PI.LevelKSplit.W.ExS.ConjNH F E σ M J := by
  intro hJ hσσ r P T hP
  have hsc : SecondCountableTopology (Af F) := PI.LevelKSplit.W.SC.finite_adeles_secondCountable F
  have hL : LCSC (HA (Af F) σ J) := PI.LevelKSplit.W.ExS.lcsc_HAf hsc
  have : BorelSpace (HA (Af F) σ J) := ⟨rfl⟩
  have : SecondCountableTopology (HA (Af F) σ J) := hL.2.1
  obtain ⟨-, cN, -⟩ := PI.LevelKSplit.W.ExC.closed_SNH hJ hσσ P T hP
  obtain ⟨lN, -⟩ := subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ _ hL cN inferInstance inferInstance
  refine conjInv_of_one _ _ lN ?_
  intro h hh
  obtain ⟨A, Z, Ψ, cA, cZ, hleft, hconj⟩ := hC hJ hσσ r P T hP
  obtain ⟨⟨lcA, scA, t2A, tgA⟩, -⟩ :=
    subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ A hL cA inferInstance inferInstance
  obtain ⟨⟨lcZ, scZ, t2Z, tgZ⟩, -⟩ :=
    subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ Z hL cZ inferInstance inferInstance
  obtain ⟨lcN, scN, t2N, tgN⟩ := lN
  have : BorelSpace A := Subtype.borelSpace _
  have : BorelSpace Z := Subtype.borelSpace _
  have : BorelSpace (Nsub (Af F) σ J P) := Subtype.borelSpace _
  have : SecondCountableTopology (Af F ⊗[F] E) := sc_tens
  have : BorelSpace (Af F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (Fin M → Af F ⊗[F] E) := Pi.borelSpace
  have H := SemiA.datR_hyp (R := Af F) hσσ hJ hP
  have cW : IsClosed ((PI.LevelKSplit.W.NC.Wp (Af F) σ J P : AddSubgroup (Fin M → Af F ⊗[F] E)) :
      Set (Fin M → Af F ⊗[F] E)) := by
    have e1 : ((PI.LevelKSplit.W.NC.Wp (Af F) σ J P : AddSubgroup (Fin M → Af F ⊗[F] E)) : Set (Fin M → Af F ⊗[F] E)) =
        {v | PI.LevelKSplit.W.NCA.DatL.pL (SemiA.datR (Af F) σ J P T) v = v} := by
      ext v
      exact mem_Wp_iff H v
    rw [e1]
    exact isClosed_eq (LinearMap.continuous_on_pi _) continuous_id
  have : LocallyCompactSpace (PI.LevelKSplit.W.NC.Wp (Af F) σ J P) := cW.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (PI.LevelKSplit.W.NC.Wp (Af F) σ J P) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  have : BorelSpace (PI.LevelKSplit.W.NC.Wp (Af F) σ J P) := Subtype.borelSpace _
  have : BorelSpace (Fin r → PI.LevelKSplit.W.NC.Wp (Af F) σ J P) := Pi.borelSpace
  have : BorelSpace ((Fin r → PI.LevelKSplit.W.NC.Wp (Af F) σ J P) × Z) := Prod.borelSpace
  have : BorelSpace (A × ((Fin r → PI.LevelKSplit.W.NC.Wp (Af F) σ J P) × Z)) := Prod.borelSpace
  let μA : Measure A := Measure.haar
  let μZ : Measure Z := Measure.haar
  let μW : Measure (PI.LevelKSplit.W.NC.Wp (Af F) σ J P) := Measure.addHaar
  let μQ : Measure (Fin r → PI.LevelKSplit.W.NC.Wp (Af F) σ J P) := Measure.pi fun _ => μW
  let ρ : Measure (A × ((Fin r → PI.LevelKSplit.W.NC.Wp (Af F) σ J P) × Z)) := μA.prod (μQ.prod μZ)
  have hΨm : Measurable Ψ := Ψ.continuous.measurable
  refine ⟨ρ.map Ψ, ?_, ?_⟩
  · have hli : (ρ.map Ψ).IsMulLeftInvariant := by
      refine ⟨fun n0 => ?_⟩
      obtain ⟨a0, t, c, ht, hc, hform⟩ := hleft n0
      have hcomm : (fun n => n0 * n) ∘ Ψ = Ψ ∘ (fun p : A × ((Fin r → PI.LevelKSplit.W.NC.Wp (Af F) σ J P) × Z) =>
          (a0 * p.1, (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2))) := by
        funext ⟨u, y, z⟩
        exact hform u y z
      have hinner : ∀ u : A, MeasurePreserving
          (fun q : (Fin r → PI.LevelKSplit.W.NC.Wp (Af F) σ J P) × Z => (q.1 + t u, c (u, q.1) * q.2))
          (μQ.prod μZ) (μQ.prod μZ) := by
        intro u
        refine (measurePreserving_add_right μQ (t u)).skew_product (g := fun y z => c (u, y) * z)
          ?_ (Filter.Eventually.of_forall fun y => map_mul_left_eq_self μZ (c (u, y)))
        exact (show Continuous fun q : (Fin r → PI.LevelKSplit.W.NC.Wp (Af F) σ J P) × Z => c (u, q.1) * q.2 from
          (hc.comp (continuous_const.prodMk continuous_fst)).mul continuous_snd).measurable
      have hgm : Continuous fun p : A × ((Fin r → PI.LevelKSplit.W.NC.Wp (Af F) σ J P) × Z) =>
          (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2) :=
        (continuous_snd.fst.add (ht.comp continuous_fst)).prodMk
          ((hc.comp (continuous_fst.prodMk continuous_snd.fst)).mul continuous_snd.snd)
      have hT : MeasurePreserving (fun p : A × ((Fin r → PI.LevelKSplit.W.NC.Wp (Af F) σ J P) × Z) =>
          (a0 * p.1, (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2))) ρ ρ :=
        (measurePreserving_mul_left μA a0).skew_product
          (g := fun (u : A) (q : (Fin r → PI.LevelKSplit.W.NC.Wp (Af F) σ J P) × Z) => (q.1 + t u, c (u, q.1) * q.2)) hgm.measurable
          (Filter.Eventually.of_forall fun u => (hinner u).map_eq)
      rw [Measure.map_map (measurable_const_mul n0) hΨm, hcomm, ← Measure.map_map hΨm hT.measurable,
        hT.map_eq]
    have hfc : IsFiniteMeasureOnCompacts (ρ.map Ψ) := Measure.IsFiniteMeasureOnCompacts.map ρ Ψ
    have hop : (ρ.map Ψ).IsOpenPosMeasure := Ψ.continuous.isOpenPosMeasure_map Ψ.surjective
    have := hfc
    have := hli
    have := hop
    exact Measure.IsHaarMeasure.mk
  · intro f hf
    have hF : Measurable fun n : Nsub (Af F) σ J P => f (h * (n : HA (Af F) σ J) * h⁻¹) :=
      hf.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
    have hF0 : Measurable fun n : Nsub (Af F) σ J P => f (n : HA (Af F) σ J) :=
      hf.comp continuous_subtype_val.measurable
    have hlinm : Measurable (linWp hh) :=
      (((LinearMap.continuous_on_pi (lin (Af F) σ J h)).comp continuous_subtype_val).subtype_mk
        _).measurable
    let Lq : (Fin r → PI.LevelKSplit.W.NC.Wp (Af F) σ J P) → (Fin r → PI.LevelKSplit.W.NC.Wp (Af F) σ J P) := fun y a => linWp hh (y a)
    have hLq : MeasurePreserving Lq μQ μQ :=
      measurePreserving_pi (fun _ => μW) (fun _ => μW)
        (fun _ => ⟨hlinm, wp_map hσσ hJ hP hV hh μW inferInstance⟩)
    have hT : MeasurePreserving (Prod.map id (Prod.map Lq id)) ρ ρ :=
      (MeasurePreserving.id μA).prod (hLq.prod (MeasurePreserving.id μZ))
    rw [lintegral_map hF hΨm, lintegral_map hF0 hΨm]
    calc ∫⁻ p, f (h * (Ψ p : HA (Af F) σ J) * h⁻¹) ∂ρ
        = ∫⁻ p, f (Ψ (Prod.map id (Prod.map Lq id) p) : HA (Af F) σ J) ∂ρ := by
          congr 1
          funext ⟨u, y, z⟩
          obtain ⟨y', hy', he⟩ := hconj h hh u y z
          have e2 : y' = Lq y := funext fun a => Subtype.ext (hy' a)
          show f (h * (Ψ (u, y, z) : HA (Af F) σ J) * h⁻¹) = f (Ψ (u, Lq y, z) : HA (Af F) σ J)
          rw [he, e2]
      _ = ∫⁻ p, f (Ψ p : HA (Af F) σ J) ∂ρ :=
          hT.lintegral_comp (show Measurable fun p => f (Ψ p : HA (Af F) σ J) from
            hf.comp (continuous_subtype_val.comp Ψ.continuous).measurable)

theorem normal_conjugation_hypothesis : NCAsm F E σ M J := fun hC hV => conjNH_of hC hV

end Af

theorem normal_conjugation_all : NCAsmAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  exact normal_conjugation_hypothesis

end PI.LevelKSplit.W.NCA
end
end

