module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0052
public import Formalism.SharpRestriction.LevelLetterCocycles.CohomologyScalarsVanish.PfCohScalarsVanish
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.H1H2LocalDuality
section
noncomputable section

namespace GlobalTheory.HOneTwoLevel

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition Topology

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem l_mem_max (N : NData R H what₂) (i : N.Loc) :
    ((N.l i : ℕ) : N.O i) ∈ IsLocalRing.maximalIdeal (N.O i) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hl : ((N.l i : ℕ) : ℤ_[N.l i]) ∈ IsLocalRing.maximalIdeal ℤ_[N.l i] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.subset_span rfl
  have hle : (⊤ : Submodule ℤ_[N.l i] (N.O i)) ≤ IsLocalRing.maximalIdeal ℤ_[N.l i] • ⊤ := by
    intro x _
    have hx : x = ((N.l i : ℕ) : ℤ_[N.l i]) • (((hu.unit⁻¹ : (N.O i)ˣ) : N.O i) * x) := by
      rw [Algebra.smul_def, map_natCast, ← mul_assoc]
      have : ((N.l i : ℕ) : N.O i) * ((hu.unit⁻¹ : (N.O i)ˣ) : N.O i) = 1 := by
        exact hu.mul_val_inv
      rw [this, one_mul]
    rw [hx]; exact Submodule.smul_mem_smul hl trivial
  have hjac : IsLocalRing.maximalIdeal ℤ_[N.l i] ≤ Ideal.jacobson ⊥ :=
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
    (Module.finite_def.1 inferInstance) hle hjac
  have h1 : (1 : N.O i) ∈ (⊤ : Submodule ℤ_[N.l i] (N.O i)) := trivial
  rw [hbot, Submodule.mem_bot] at h1
  exact one_ne_zero h1

theorem isLocalHom (N : NData R H what₂) (i : N.Loc) : IsLocalHom (algebraMap ℤ_[N.l i] (N.O i)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have ha' : a ∈ IsLocalRing.maximalIdeal ℤ_[N.l i] := (IsLocalRing.mem_maximalIdeal a).2 h
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at ha'
  obtain ⟨c, rfl⟩ := ha'
  have : algebraMap ℤ_[N.l i] (N.O i) (c * (N.l i : ℤ_[N.l i])) ∈ IsLocalRing.maximalIdeal (N.O i) := by
    rw [map_mul, map_natCast]; exact Ideal.mul_mem_left _ _ (l_mem_max N i)
  exact (IsLocalRing.mem_maximalIdeal _).1 this ha

theorem resFin (N : NData R H what₂) (i : N.Loc) : Finite (IsLocalRing.ResidueField (N.O i)) :=
  haveI := isLocalHom N i
  IsLocalRing.ResidueField.finite_of_finite (R := ℤ_[N.l i]) inferInstance

theorem resChar (N : NData R H what₂) (i : N.Loc) : CharP (IsLocalRing.ResidueField (N.O i)) (N.l i) := by
  rw [CharP.charP_iff_prime_eq_zero (N.lPrime i).out, ← map_natCast (IsLocalRing.residue (N.O i)),
    IsLocalRing.residue_eq_zero_iff]
  exact l_mem_max N i

theorem residue_eq_one (N : NData R H what₂) (i : N.Loc) {x : N.O i}
    (hx : x - 1 ∈ IsLocalRing.maximalIdeal (N.O i)) : IsLocalRing.residue (N.O i) x = 1 := by
  rw [← sub_eq_zero, ← map_one (IsLocalRing.residue (N.O i)), ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hx

theorem chiEpsBar_open (N : NData R H what₂) (i : N.Loc) (e : ℤ) :
    IsOpen ((Formalism.MainNotions.SumRepresentations.At.chiEpsBar N i e).ker : Set (G H.E N.Om)) := by
  have hm : IsOpen (IsLocalRing.maximalIdeal (N.O i) : Set (N.O i)) := by
    have := (isAdic_iff.1 (N.O_adic i)).1 1
    rwa [pow_one] at this
  have hmZ : IsOpen (IsLocalRing.maximalIdeal ℤ_[N.l i] : Set ℤ_[N.l i]) := by
    have : (IsLocalRing.maximalIdeal ℤ_[N.l i] : Set ℤ_[N.l i]) = {x | ‖x‖ < 1} := by
      ext x
      simp only [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, Set.mem_setOf_eq]
      exact PadicInt.mem_nonunits
    rw [this]; exact isOpen_lt continuous_norm continuous_const
  let U1 : Set (G H.E N.Om) :=
    (fun g => ((N.chi i 1 g : (N.O i)ˣ) : N.O i) - 1) ⁻¹' (IsLocalRing.maximalIdeal (N.O i) : Set (N.O i))
  let U2 : Set (G H.E N.Om) :=
    (fun g => ((cycZ H.E N.Om (N.l i) g : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) - 1) ⁻¹'
      (IsLocalRing.maximalIdeal ℤ_[N.l i] : Set ℤ_[N.l i])
  have hU1 : IsOpen U1 := hm.preimage ((N.chi_cont i 1).sub continuous_const)
  have hU2 : IsOpen U2 :=
    hmZ.preimage ((Units.continuous_val.comp (continuous_cycZ H.E N.Om (N.l i))).sub continuous_const)
  have h1 : (1 : G H.E N.Om) ∈ U1 ∩ U2 := by
    refine ⟨?_, ?_⟩
    · show ((N.chi i 1 1 : (N.O i)ˣ) : N.O i) - 1 ∈ IsLocalRing.maximalIdeal (N.O i)
      rw [map_one, Units.val_one, sub_self]; exact Ideal.zero_mem _
    · show ((cycZ H.E N.Om (N.l i) 1 : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[N.l i]
      rw [map_one, Units.val_one, sub_self]; exact Ideal.zero_mem _
  have hsub : U1 ∩ U2 ⊆ ((Formalism.MainNotions.SumRepresentations.At.chiEpsBar N i e).ker : Set (G H.E N.Om)) := by
    intro g hg
    have ha : Units.map (IsLocalRing.residue (N.O i)).toMonoidHom (N.chi i 1 g) = 1 := by
      ext
      exact residue_eq_one N i hg.1
    have hb : Units.map (IsLocalRing.residue (N.O i)).toMonoidHom (Formalism.MainNotions.N.Glob.epsO N i g) = 1 := by
      ext
      apply residue_eq_one N i
      have := isLocalHom N i
      have h2 : ((cycZ H.E N.Om (N.l i) g : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) - 1 ∈
          IsLocalRing.maximalIdeal ℤ_[N.l i] := hg.2
      have h3 : algebraMap ℤ_[N.l i] (N.O i)
          (((cycZ H.E N.Om (N.l i) g : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) - 1) ∈ IsLocalRing.maximalIdeal (N.O i) :=
        (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
          (IsLocalRing.mem_maximalIdeal _).1 h2 (isUnit_of_map_unit _ _ hu)
      rw [map_sub, map_one] at h3
      exact h3
    show Formalism.MainNotions.SumRepresentations.At.chiEpsBar N i e g = 1
    delta Formalism.MainNotions.SumRepresentations.At.chiEpsBar
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.zpow_apply, MonoidHom.comp_apply,
      MonoidHom.comp_apply, ha, hb, inv_one, one_zpow, one_mul]
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset ((hU1.inter hU2).mem_nhds h1) hsub)

theorem contAction_of_open {k Γ M : Type} [CommRing k] [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation k Γ M) (U : Subgroup Γ) (hU : IsOpen (U : Set Γ))
    (h1 : ∀ u ∈ U, rho u = 1) : ReciprocityTheory.Gal.ContAction rho := by
  unfold ReciprocityTheory.Gal.ContAction
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨g, m⟩
  have hU' : (fun x : Γ => g⁻¹ * x) ⁻¹' (U : Set Γ) ∈ 𝓝 g :=
    (hU.preimage (continuous_const.mul continuous_id)).mem_nhds (by simpa using U.one_mem)
  have hm : ({m} : Set M) ∈ 𝓝 m := (isOpen_discrete _).mem_nhds rfl
  filter_upwards [prod_mem_nhds hU' hm] with x hx
  have hx2' : x.2 = m := hx.2
  have hx1' : g⁻¹ * x.1 ∈ U := hx.1
  show rho x.1 x.2 = rho g m
  calc rho x.1 x.2 = rho (g * (g⁻¹ * x.1)) m := by rw [mul_inv_cancel_left, hx2']
    _ = rho g (rho (g⁻¹ * x.1) m) := by rw [map_mul]; rfl
    _ = rho g m := by rw [h1 _ hx1']; rfl

theorem twist_sub_bijective {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k) (c : k) (hc : c ≠ 0)
    (hne : ¬ A.charpoly.IsRoot c) :
    Function.Bijective (fun v : Fin n → k => c⁻¹ • Matrix.toLin' A v - v) := by
  let f : (Fin n → k) →ₗ[k] (Fin n → k) := c⁻¹ • Matrix.toLin' A - LinearMap.id
  have hf : ∀ v, f v = c⁻¹ • Matrix.toLin' A v - v := fun v => rfl
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker, hf, sub_eq_zero] at hv
    rw [Submodule.mem_bot]
    by_contra h0
    apply hne
    rw [← Matrix.charpoly_toLin', ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    have hAv : Matrix.toLin' A v = c • v := by
      calc Matrix.toLin' A v = c • (c⁻¹ • Matrix.toLin' A v) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
        _ = c • v := by rw [hv]
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 hAv, h0⟩
  have hbij : Function.Bijective f := ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  exact hbij

theorem hOneTwo_holds : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ D : D7, HOneTwo D := by
  intro hF hT hE D i rb w hwS hrb hnr e
  have hw : w ∉ placesOver D.host.E (D.nd.l i) := D.nd.SQ_l i w (Or.inl hwS)
  haveI := resFin D.nd i
  haveI := resChar D.nd i
  letI : TopologicalSpace (IsLocalRing.ResidueField (D.nd.O i)) := ⊥
  haveI : DiscreteTopology (IsLocalRing.ResidueField (D.nd.O i)) := ⟨rfl⟩
  haveI : CharP (IsLocalRing.ResidueField (D.nd.O i)) (D.nd.l i ^ 1) := by rw [pow_one]; infer_instance
  letI : Module (ZMod (D.nd.l i ^ 1)) (Fin D.R.r → IsLocalRing.ResidueField (D.nd.O i)) :=
    Module.compHom _ (ZMod.castHom (dvd_refl _) (IsLocalRing.ResidueField (D.nd.O i)))
  haveI : ContinuousConstSMul (ZMod (D.nd.l i ^ 1)) (Fin D.R.r → IsLocalRing.ResidueField (D.nd.O i)) :=
    ⟨fun _ => continuous_of_discreteTopology⟩
  let rho := (Formalism.MainNotions.N.twistRep (Formalism.MainNotions.N.glRep rb) (Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i e)).comp
    (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype
  let rhoZ : Representation (ZMod (D.nd.l i ^ 1)) ↥(Dec (F := D.host.E) (D.nd.plOm.1 w))
      (Fin D.R.r → IsLocalRing.ResidueField (D.nd.O i)) :=
    { toFun := fun g =>
        { toFun := rho g
          map_add' := map_add (rho g)
          map_smul' := fun c m => map_smul (rho g)
            (ZMod.castHom (dvd_refl _) (IsLocalRing.ResidueField (D.nd.O i)) c) m }
      map_one' := LinearMap.ext fun m => show rho 1 m = m by rw [map_one]; rfl
      map_mul' := fun g h => LinearMap.ext fun m => show rho (g * h) m = rho g (rho h m) by
        rw [map_mul]; rfl }
  have hrZ : ∀ g m, rhoZ g m = rho g m := fun _ _ => rfl

  have hU : IsOpen (((rb.ker ⊓ (Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i e).ker).comap
      (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype : Subgroup _) :
        Set ↥(Dec (F := D.host.E) (D.nd.plOm.1 w))) :=
    (hrb.1.inter (chiEpsBar_open D.nd i e)).preimage continuous_subtype_val
  have h1U : ∀ u ∈ ((rb.ker ⊓ (Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i e).ker).comap
      (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype), rhoZ u = 1 := by
    intro u hu
    have hu' := Subgroup.mem_inf.1 (Subgroup.mem_comap.1 hu)
    have ha : rb (u : G D.host.E D.nd.Om) = 1 := MonoidHom.mem_ker.1 hu'.1
    have hc : Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i e (u : G D.host.E D.nd.Om) = 1 := MonoidHom.mem_ker.1 hu'.2
    apply LinearMap.ext
    intro v
    show ((Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i e (u : G D.host.E D.nd.Om) :
        (IsLocalRing.ResidueField (D.nd.O i))ˣ) : IsLocalRing.ResidueField (D.nd.O i)) •
        Matrix.toLin' ((rb (u : G D.host.E D.nd.Om) : GL _ _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O i))) v = v
    rw [ha, hc]
    simp
  have hcZ : ContAction rhoZ := contAction_of_open _ _ hU h1U

  have hγD : D.nd.gam0 i w ∈ Dec (F := D.host.E) (D.nd.plOm.1 w) := Ine_le_Dec _ (D.nd.locNd_chebotarevPlace_mem i w)
  have hc0 : IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w)) ≠ 0 :=
    ((Units.isUnit (D.nd.chi i 1 (D.nd.gam0 i w))).map (IsLocalRing.residue (D.nd.O i))).ne_zero
  have hbij : Function.Bijective (fun v : Fin D.R.r → IsLocalRing.ResidueField (D.nd.O i) =>
      rhoZ ⟨D.nd.gam0 i w, hγD⟩ v - v) := by
    have h2 : (fun v : Fin D.R.r → IsLocalRing.ResidueField (D.nd.O i) =>
        rhoZ ⟨D.nd.gam0 i w, hγD⟩ v - v) = fun v =>
        (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w)))⁻¹ •
          Matrix.toLin' ((rb (D.nd.gam0 i w) : GL _ _) :
          Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O i))) v - v := by
      funext v
      show ((Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i e (D.nd.gam0 i w) : (IsLocalRing.ResidueField (D.nd.O i))ˣ) :
        IsLocalRing.ResidueField (D.nd.O i)) • Matrix.toLin' ((rb (D.nd.gam0 i w) : GL _ _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O i))) v - v = _
      rw [Formalism.MainNotions.SumRepresentations.twisted_character_at_frobenius D.nd w hw e]
    rw [h2]
    exact twist_sub_bijective _ _ hc0 hnr
  have key := GlobalTheory.T.localCohomology_vanishes_tame_inertia_no_fixed hF hT hE D.host.E D.nd.Om (D.nd.l i)
    (Fin D.R.r → IsLocalRing.ResidueField (D.nd.O i)) (D.nd.plOm.1 w) w rhoZ (D.nd.plOm.2 w) hw hcZ
    ⟨⟨D.nd.gam0 i w, hγD⟩, D.nd.locNd_chebotarevPlace_mem i w, hbij⟩
  have hk := Formalism.MainNotions.N.CohomologyScalarsVanish.cohScalarsVanish (D.nd.l i ^ 1) (IsLocalRing.ResidueField (D.nd.O i))
    ↥(Dec (F := D.host.E) (D.nd.plOm.1 w)) (Fin D.R.r → IsLocalRing.ResidueField (D.nd.O i)) rho rhoZ hrZ key
  exact ⟨hk.2.1, hk.2.2⟩

end GlobalTheory.HOneTwoLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtNatCast
section
open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory.GO.ChRoot

section Loc

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

theorem intAt_natCast (k : ℕ) : IntAt P (k : E) := by simpa using IntAt.coe P (k : 𝓞 E)

theorem intAt_zero' : IntAt P (0 : E) := by simpa using intAt_natCast (P := P) 0

theorem intAt_one' : IntAt P (1 : E) := by simpa using intAt_natCast (P := P) 1

theorem qOf_pos (P : HeightOneSpectrum (𝓞 E)) : 0 < qOf P :=
  Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

variable [StarRing E]

theorem mem_stdAt' {n : ℕ} {x : Sp E n} : x ∈ stdAt E n P ↔ ∀ i, IntAt P (x i) := mem_localization_standardLattice P x

theorem mem_lamY_zero {q n c : ℕ} {x : Sp E (n + c)} : x ∈ LocE.lamY P q n c 0 ↔ x ∈ stdAt E (n + c) P := by
  unfold LocE.lamY LocE.sclLat
  rw [Submodule.mem_comap, mem_stdAt', mem_stdAt']
  refine forall_congr' fun i => ?_
  simp [LocE.scE]

theorem eN_mem {N i : ℕ} : Loc.eN E N i ∈ stdAt E N P := by
  rw [mem_stdAt']
  intro l
  unfold Loc.eN
  split_ifs
  · exact intAt_one'
  · exact intAt_zero'

theorem intAt_n1Arg {n c : ℕ} (a : E) (r : Sp E (n + c) ≃ₗ[E] Sp E (n + c))
    (h : ∀ x ∈ stdAt E (n + c) P, a • r x ∈ stdAt E (n + c) P) : IntAt P (a * Loc.n1Arg r) := by
  unfold Loc.n1Arg
  rw [Finset.mul_sum]
  refine Finset.sum_induction _ (IntAt P) (fun _ _ ha hb => ha.add hb) intAt_zero' fun i _ => ?_
  unfold Loc.atN
  split_ifs with hi
  · exact mem_stdAt'.1 (h _ eN_mem) ⟨n + i, hi⟩
  · simpa using intAt_zero'


omit [StarRing E] in
theorem unitV_root {K : Type} [Field K] (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) (h : LocE.unitV χ a ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ LocE.unitV χ a ^ k = 1 := by
  unfold LocE.unitV at h ⊢
  split_ifs at h ⊢ with hu
  · have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
    refine ⟨Nat.card (𝓞 E ⧸ P.asIdeal)ˣ, Nat.card_pos, ?_⟩
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  · exact absurd rfl h

end Loc

theorem psi_root {X : Fields} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {c : LocCst X SB} (hc : c.Ok) (P : SB) (x : X.E)
    (hx : IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * x)) : c.psi P x ^ (qOf P.1 ^ c.D P) = 1 := by
  have key : ∀ k : ℕ, c.psi P ((k : X.E) * x) = c.psi P x ^ k := by
    intro k
    induction k with
    | zero => simpa using hc.psi_int P 0 intAt_zero'
    | succ k ih =>
      rw [Nat.cast_succ, add_mul, one_mul, hc.psi_add P _ _ _ hx, ih, pow_succ]
      rw [mul_left_comm]
      exact (intAt_natCast k).mul hx
  rw [← key]
  exact hc.psi_int P _ (by simpa using hx)

theorem lam_root {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    (hL : L.Ok Ch sel mu cst G m2) {j : ℕ} (hj : j ≤ m2 + 1) (b : L.β j)
    (P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}) (hP : P.1 ∉ Pr.vGs) (g : (L.levQ j b P).H) :
    ∃ k : ℕ, 0 < k ∧ (L.levQ j b P).lam g ^ k = 1 := by
  classical
  have hg := Subgroup.mem_subgroupOf.1 ((hL.grpQ j b P).le g.2)
  obtain ⟨r, hr, hrg⟩ := hg
  let P' : rowSG Pr sel mu := ⟨P.1, Finset.mem_union_right _ P.2⟩
  obtain ⟨h, hh⟩ : ∃ h, h = L.h j b P' := ⟨_, rfl⟩
  have hχ : (((L.levQ j b P).lam g : X.Kˣ) : X.K) = chiInv Ch sel mu cst j P' (L.h j b P') r := hL.chrQ j b P g r hr hrg
  replace hr : r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h := hh ▸ hr
  rw [← hh] at hχ
  have hb := hL.boundQ j b P' hP
  have hD := hL.depthQ' P' hP
  have hm := hL.hm
  simp only [lamYat, show P'.1 ∉ Pr.vGs from hP, if_false, mem_lamY_zero] at hb
  have hκ := hr.2
  simp only [Jat, hP, if_false] at hκ
  have hκ' : ∀ x, (h⁻¹ * r * h) x ∈ stdAt X.E _ P.1 ↔ x ∈ stdAt X.E _ P.1 := by
    intro x
    exact hκ.1 x
  have hint : IntAt P.1 ((qOf P.1 : X.E) ^ j * Loc.n1Arg r) := by
    refine intAt_n1Arg _ r fun x hx => ?_
    have h1 := (hb _ ((hκ' _).2 (hb x hx).1)).2
    have h2 : h ((h⁻¹ * r * h) (h⁻¹ x)) = r x := by
      change (h * (h⁻¹ * r * h) * h⁻¹) x = r x
      congr 1
      group
    rwa [← hh, h2] at h1
  have hint' : IntAt P'.1 ((qOf P'.1 : X.E) ^ cst.D P' * Loc.n1Arg r) := by
    obtain ⟨d, hd⟩ : ∃ d, cst.D P' = d + j := ⟨cst.D P' - j, by omega⟩
    rw [hd, pow_add, mul_assoc, ← Nat.cast_pow]
    exact (intAt_natCast _).mul hint
  have h1 := psi_root hL.cst_ok P' _ hint'
  simp only [chiInv, lamRow, show P'.1 ∉ Pr.vGs from hP, if_false, LocE.lamQB] at hχ
  have hne := ((L.levQ j b P).lam g).ne_zero
  rw [hχ] at hne
  obtain ⟨k, hk, h2⟩ := unitV_root _ _ (fun h0 => right_ne_zero_of_mul hne (inv_eq_zero.2 h0))
  refine ⟨qOf P'.1 ^ cst.D P' * k, Nat.mul_pos (pow_pos (qOf_pos _) _) hk, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, hχ, mul_pow, inv_pow, inv_pow, pow_mul, h1, one_pow, mul_comm _ k, pow_mul, h2, one_pow]
  simp

end GlobalTheory.GO.ChRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralDivUniformizerOfRedZero
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.TypePrimeUnif


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq {X : _root_.Formalism.L2.Col.Fields} (hX : X.Ok) {Pr : _root_.Formalism.L2.Col.Primes X}
    (hP : Pr.Ok) (i : Fin 2) (P : HeightOneSpectrum (𝓞 X.E))
    (hv : P ∈ Pr.vG i) : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal ∧ ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 := by
  classical
  refine ⟨hP.g_mem hv, fun hsq => ?_⟩
  have hdiv : ∀ Q ∈ Pr.vG i, X.conjO (Pr.piG i) ∈ Q.asIdeal := fun Q hQ =>
    _root_.Formalism.L2.Col.decoFin_mem_of_mem_divs (show Q ∈ _root_.Formalism.L2.Col.divs (X.conjO (Pr.piG i)) from hQ)
  have hg1 : 1 < Pr.g i := (hP.g_prime i).one_lt
  have hN : Ideal.absNorm (Ideal.span {X.conjO (Pr.piG i)}) = Pr.g i ^ X.f := by
    have h1 : Ideal.absNorm (Ideal.span {Pr.piG i}) * Ideal.absNorm (Ideal.span {X.conjO (Pr.piG i)})
        = Pr.g i ^ (2 * X.f) := by
      rw [← map_mul, Ideal.span_singleton_mul_span_singleton, hP.piG_norm i, X.absNorm_nat, hX.rankQ]
    rw [X.absNorm_conjO, ← sq, pow_mul'] at h1
    rw [X.absNorm_conjO]
    exact Nat.pow_left_injective two_ne_zero h1
  have hπP : Pr.piG i ∉ P.asIdeal := fun h => by
    obtain ⟨a, b, hab⟩ := hP.piG_cop i
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left a h) (P.asIdeal.mul_mem_left b (hdiv P hv))
  have hcop : IsCoprime (P.asIdeal ^ 2) (Ideal.span {Pr.piG i}) := by
    apply IsCoprime.pow_left
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have heq := P.isMaximal.eq_of_le h le_sup_left
    exact hπP (by rw [heq]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hP2 : P.asIdeal ^ 2 ∣ Ideal.span {X.conjO (Pr.piG i)} := by
    have h : P.asIdeal ^ 2 ∣ Ideal.span {Pr.piG i} * Ideal.span {X.conjO (Pr.piG i)} := by
      rw [Ideal.span_singleton_mul_span_singleton, hP.piG_norm i, Ideal.dvd_span_singleton]
      exact hsq
    first
      | exact hcop.dvd_of_dvd_mul_left h
      | exact hcop.dvd_of_dvd_mul_right h
  let e : HeightOneSpectrum (𝓞 X.E) → ℕ := fun Q => if Q = P then 2 else 1
  have hall : ∏ Q ∈ Pr.vG i, Q.asIdeal ^ e Q ∣ Ideal.span {X.conjO (Pr.piG i)} := by
    apply Finset.prod_dvd_of_coprime
    · intro Q _ Q' _ hne
      simp only [Function.onFun]
      apply IsCoprime.pow
      rw [Ideal.isCoprime_iff_sup_eq]
      exact Ideal.IsMaximal.coprime_of_ne Q.isMaximal Q'.isMaximal
        (fun h => hne (HeightOneSpectrum.ext h))
    · intro Q hQ
      by_cases h : Q = P
      · subst h
        simpa [e] using hP2
      · simpa [e, h, Ideal.dvd_span_singleton] using hdiv Q hQ
  have hnorm := map_dvd Ideal.absNorm hall
  rw [map_prod, hN] at hnorm
  have hcount : ∏ Q ∈ Pr.vG i, Ideal.absNorm (Q.asIdeal ^ e Q) = Pr.g i ^ (X.f + 1) := by
    rw [Finset.prod_congr rfl (fun Q hQ => show Ideal.absNorm (Q.asIdeal ^ e Q) = Pr.g i ^ e Q by
      rw [map_pow, hP.vG_norm i Q hQ]), Finset.prod_pow_eq_pow_sum]
    congr 1
    have he : ∀ Q, e Q = 1 + if Q = P then 1 else 0 := fun Q => by
      by_cases h : Q = P <;> simp [e, h]
    simp only [he, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.sum_ite_eq', hv, if_true, hP.vG_card i]
  rw [hcount] at hnorm
  have := (Nat.pow_dvd_pow_iff_le_right hg1).mp hnorm
  omega


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.TypePrimeUnif.intAt_div_of_notMem_sq {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (g : 𝓞 E)
    (h1 : g ∈ w.asIdeal) (h2 : g ∉ w.asIdeal ^ 2) (a : E) (ha : _root_.Formalism.L2.Col.IntAt w a) (h0 : _root_.Formalism.L2.Col.redP w a = 0) :
    _root_.Formalism.L2.Col.IntAt w (a / algebraMap (𝓞 E) E g) := by
  haveI := w.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  have key : ∃ c r, ∃ s ∉ w.asIdeal, algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk w.asIdeal s * c = Ideal.Quotient.mk w.asIdeal r := by
    obtain ⟨r, s, hs, hsr⟩ := ha
    have hs0 : Ideal.Quotient.mk w.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
    exact ⟨(Ideal.Quotient.mk w.asIdeal s)⁻¹ * Ideal.Quotient.mk w.asIdeal r, r, s, hs, hsr,
      mul_inv_cancel_left₀ hs0 _⟩
  unfold _root_.Formalism.L2.Col.redP at h0
  rw [dite_eq_left key] at h0
  have hspec := key.choose_spec
  rw [h0] at hspec
  obtain ⟨r, s, hs, hsr, hc⟩ := hspec
  rw [mul_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at hc
  obtain ⟨J, hJ⟩ := (Ideal.dvd_span_singleton (I := w.asIdeal) (x := g)).mpr h1
  have hJw : ¬ J ≤ w.asIdeal := fun hle => h2 (by
    rw [sq]
    exact Ideal.mul_mono_right hle (hJ ▸ Ideal.mem_span_singleton_self g))
  obtain ⟨t, htJ, htw⟩ := Set.not_subset.mp hJw
  have hrt : r * t ∈ Ideal.span {g} := hJ ▸ Ideal.mul_mem_mul hc htJ
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hrt
  have hg0 : algebraMap (𝓞 E) E g ≠ 0 := by
    intro h
    apply h2
    rw [(IsFractionRing.injective (𝓞 E) E) (h.trans (map_zero _).symm)]
    exact zero_mem _
  refine ⟨x, s * t, fun hst => (w.isPrime.mem_or_mem hst).elim hs htw, ?_⟩
  have hxE : algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E g =
      algebraMap (𝓞 E) E r * algebraMap (𝓞 E) E t := by
    rw [← map_mul, ← map_mul, hx]
  have hmain : algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E t * a =
      algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E g := by
    linear_combination algebraMap (𝓞 E) E t * hsr - hxE
  calc algebraMap (𝓞 E) E (s * t) * (a / algebraMap (𝓞 E) E g)
      = algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E t * a / algebraMap (𝓞 E) E g := by
        rw [map_mul]; ring
    _ = algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E g / algebraMap (𝓞 E) E g := by rw [hmain]
    _ = algebraMap (𝓞 E) E x := mul_div_cancel_right₀ _ hg0


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.TypePrimeUnif.intAt_div_qOf : ∀ (X : _root_.Formalism.L2.Col.Fields) (Pr : _root_.Formalism.L2.Col.Primes X), X.Ok → Pr.Ok →
    ∀ w ∈ Pr.vGs, ∀ a : X.E, _root_.Formalism.L2.Col.IntAt w a →
    _root_.Formalism.L2.Col.redP w a = 0 → _root_.Formalism.L2.Col.IntAt w (a / (_root_.Formalism.L2.Col.qOf w : X.E)) := by
  classical
  intro X Pr hX hP w hw a ha h0
  have hw' : w ∈ Pr.vG 0 ∪ Pr.vG 1 := hw
  obtain ⟨i, hv⟩ : ∃ i, w ∈ Pr.vG i := by
    rcases Finset.mem_union.mp hw' with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hq : (_root_.Formalism.L2.Col.qOf w : X.E) = algebraMap (𝓞 X.E) X.E ((Pr.g i : ℕ) : 𝓞 X.E) := by
    unfold _root_.Formalism.L2.Col.qOf
    rw [map_natCast, hP.vG_norm i w hv]
  have hgw := _root_.GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq hX hP i w hv
  rw [hq]
  exact _root_.GlobalTheory.TypePrimeUnif.intAt_div_of_notMem_sq w _ hgw.1 hgw.2 a ha h0

end GlobalTheory.TypePrimeUnif
end

