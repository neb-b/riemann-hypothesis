module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0407
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAutomorphicSideEmptyLocal
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem autIso_symm {π π' : NG.AutRep L n} (h : π.Iso π') : π'.Iso π := (NG.AutRep.iso_equivalence (L := L) (n := n)).symm h

theorem autIso_trans {π π' π'' : NG.AutRep L n} (h : π.Iso π') (h' : π'.Iso π'') : π.Iso π'' :=
  (NG.AutRep.iso_equivalence (L := L) (n := n)).trans h h'

theorem clsA_eq_iff (π π' : NG.AutRep L n) : clsA π = clsA π' ↔ π.Iso π' := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := _root_.GlobalTheory.AutModel.exists_autRepM L n π'
    have h2 : m ∈ (clsA π).1 := by rw [h]; exact hm
    exact autIso_trans h2 (autIso_symm hm)
  · intro h
    apply Subtype.ext
    ext m
    exact ⟨fun h' => autIso_trans (autIso_symm h) h', fun h' => autIso_trans h h'⟩

theorem clsW_eq_iff (a b : NG.AlgWt L n) : clsW a = clsW b ↔ a.Iso b := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := _root_.GlobalTheory.AutQuot.Model.exists_model L n b
    have h2 : m ∈ (clsW a).1 := by rw [h]; exact hm
    exact h2.trans hm.symm
  · intro h
    apply Subtype.ext
    ext m
    exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

theorem rep_iso (π : NG.AutRep L n) : (clsA π).rep.Iso π :=
  (clsA_eq_iff _ _).1 (AUq.cls_rep (clsA π))

theorem repW_iso (a : NG.AlgWt L n) : (clsW a).rep.Iso a :=
  (clsW_eq_iff _ _).1 (WtQ.cls_rep (clsW a))

theorem sphAt_iso {π π' : NG.AutRep L n} (h : π.Iso π') {v} (hs : π.SphAt v) : π'.SphAt v := by
  obtain ⟨-, T, hT⟩ := h
  obtain ⟨f, hf, hf0, hfix⟩ := hs
  refine ⟨(T ⟨f, hf⟩ : _), (T ⟨f, hf⟩).2, ?_, fun κ hκ ht => ?_⟩
  · intro h0
    apply hf0
    have : T ⟨f, hf⟩ = 0 := Subtype.ext h0
    have := congrArg Subtype.val (T.injective (this.trans T.map_zero.symm))
    exact this
  · have := hT κ ⟨f, hf⟩ ⟨f, hf⟩ (hfix κ hκ ht).symm
    exact this.symm

omit [NumberField L] [IsCMField L] in
theorem overPl_unique {w : HeightOneSpectrum (𝓞 L)} {v v' : HeightOneSpectrum (𝓞 (maximalRealSubfield L))}
    (h : NG.OverPl w v) (h' : NG.OverPl w v') : v = v' :=
  HeightOneSpectrum.ext (h.symm.trans h')

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem locAt_of_split (π : NG.AutRep L n) (s : SplitPlace L) : ∃ x, LocAt π s.w x := by
  obtain ⟨σ, hσ, -⟩ := _root_.GlobalTheory.LocCompSplit.main L n π s
  exact ⟨_, s, σ, rfl, hσ, HEq.rfl⟩

theorem locAt_unique {π π' : NG.AutRep L n} (hi : π.Iso π') {w : HeightOneSpectrum (𝓞 L)} {x x'}
    (hx : LocAt π w x) (hx' : LocAt π' w x') : x = x' := by
  obtain ⟨s, σ, hs, hσ, e⟩ := hx
  obtain ⟨s', σ', hs', hσ', e'⟩ := hx'
  obtain ⟨σ₀, -, hu⟩ := _root_.GlobalTheory.LocCompSplit.main L n π s
  have h1 := hu π s rfl σ ((NG.AutRep.iso_equivalence (L := L) (n := n)).refl π) hσ
  have h2 := hu π' s' (hs'.trans hs.symm) σ' hi hσ'
  have key : ∀ (u u' : HeightOneSpectrum (𝓞 L)) (_ : u = u') (a : GlobalTheory.SmGL.IrrCl (GL (Fin n) (u.adicCompletion L)))
      (b : GlobalTheory.SmGL.IrrCl (GL (Fin n) (u'.adicCompletion L))), HEq a b →
      HEq (⟨n, a⟩ : GlobalTheory.LocGL.IrrGL (k := u.adicCompletion L)) (⟨n, b⟩ : GlobalTheory.LocGL.IrrGL (k := u'.adicCompletion L)) := by
    intro u u' hu a b hab
    subst hu
    cases eq_of_heq hab
    rfl
  have h3 : HEq (GlobalTheory.LocLanglands.cls σ) (GlobalTheory.LocLanglands.cls σ') :=
    key _ _ (hs.trans hs'.symm) _ _ (h1.trans h2.symm)
  exact eq_of_heq (e.symm.trans (h3.trans e'))

end

end GlobalTheory.AutQuot

namespace GlobalTheory.AutQuot

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable (D : D7)

theorem f_sat (π : NG.AutRep D.host.E D.R.nV) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (w : PlE D.host)
    (hv : NG.OverPl w v) (Dv : InertDatum D.host.E D.R.nV v w) (hα : ∃ α, NG.SatAt π Dv α) :
    ∃ α, NG.SatAt π Dv α ∧ satOf (clsA π).rep w = Finset.univ.val.map α := by
  obtain ⟨α, hα⟩ := hα
  have hex : ∃ (v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (Dv' : InertDatum D.host.E D.R.nV v' w)
      (α' : Fin (D.R.nV / 2) → ℂ), NG.OverPl w v' ∧ NG.SatAt (clsA π).rep Dv' α' :=
    ⟨v, Dv, α, hv, _root_.GlobalTheory.SatInd.satAt_indep _ _ π _ (autIso_symm (rep_iso π)) v w hv Dv Dv α hα⟩
  unfold satOf
  rw [dite_eq_left hex]
  have key : ∀ (v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (Dv' : InertDatum D.host.E D.R.nV v' w)
      (α' : Fin (D.R.nV / 2) → ℂ), NG.OverPl w v' → NG.SatAt (clsA π).rep Dv' α' → NG.SatAt π Dv α' := by
    intro v' Dv' α' hv' hs'
    have e := overPl_unique hv hv'
    subst e
    exact _root_.GlobalTheory.SatInd.satAt_indep _ _ _ π (rep_iso π) v w hv _ Dv _ hs'
  obtain ⟨hv', hs'⟩ := hex.choose_spec.choose_spec.choose_spec
  exact ⟨_, key _ _ _ hv' hs', rfl⟩

theorem f_wt (π : NG.AutRep D.host.E D.R.nV) (a : NG.AlgWt D.host.E D.R.nV) (hd : π.toAlgWt.IsDual a) :
    wtOf D (clsA π).rep = clsW a := by
  have hπ : (clsA π).rep.toAlgWt.Iso π.toAlgWt := (rep_iso π).1
  obtain ⟨b, hb, hbu, hba⟩ := _root_.GlobalTheory.algWt_contragredient _ _ π.toAlgWt
  have hrb : (clsA π).rep.toAlgWt.IsDual b := (hba _ hπ.symm).1
  have hex : ∃ b, (clsA π).rep.toAlgWt.IsDual b := ⟨b, hrb⟩
  unfold wtOf
  rw [dite_eq_left hex]
  obtain ⟨b', -, hbu', -⟩ := _root_.GlobalTheory.algWt_contragredient _ _ (clsA π).rep.toAlgWt
  have h1 : b'.Iso hex.choose := (hbu' _).1 hex.choose_spec
  have h2 : b'.Iso b := (hbu' _).1 hrb
  have h3 : b.Iso a := (hbu a).1 hd
  exact (clsW_eq_iff _ _).2 ((h1.symm.trans h2).trans h3)

theorem f_infW (a : NG.AlgWt D.host.E D.R.nV) (τ : D.host.E →+* ℂ) (lam : Fin D.R.nV → ℤ) (hl : a.HWAt τ lam) :
    NG.infOf (hwOf (clsW a).rep τ) = NG.infOf lam := by
  have hi : a.Iso (clsW a).rep := (repW_iso a).symm
  obtain ⟨b0, hb0, hb0', hhw⟩ := _root_.GlobalTheory.algWt_contragredient _ _ a
  have hr : (clsW a).rep.HWAt τ lam := ((hhw _ hi).2 τ lam hl)
  obtain ⟨huniq, hanti⟩ := _root_.GlobalTheory.AlgWtHW.hw_exists_unique_antitone _ _ (clsW a).rep τ
  have hex : ∃ lam, (clsW a).rep.HWAt τ lam ∧ Antitone lam := ⟨lam, hr, hanti lam hr⟩
  unfold hwOf
  rw [dite_eq_left hex, huniq.unique hex.choose_spec.1 hr]

end

end GlobalTheory.AutQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartFromAdelicDictionary
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopCh

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem localComponent_congr {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)} (hP : P.under (𝓞 F) = v)
    {x x' : GL (Fin n) (AfE F E)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') : rhoP F P x = rhoP F P x' := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have h0 : prV (E := E) v ((x : Matrix (Fin n) (Fin n) (AfE F E)) i j) = prV (E := E) v ((x' : Matrix (Fin n) (Fin n) (AfE F E)) i j) :=
    congrArg (fun g : GL (Fin n) (E ⊗[F] v.adicCompletion F) => (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j) h
  have h1 : prV (E := E) v ((x : Matrix (Fin n) (Fin n) (AfE F E)) i j - (x' : Matrix (Fin n) (Fin n) (AfE F E)) i j) = 0 := by
    rw [map_sub, h0, sub_self]
  have h2 := (GlobalTheory.T.placeProjection_zero_integral_iff_components_above F E v _).1.1 h1 P hP
  rw [map_sub, sub_eq_zero] at h2
  exact h2

end SlopeTestRemainingChoices

section Dense

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
  {hc : CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem valuation_entries_le_one_of_mem_levelGroupOne {z : GL (Fin n) (AfE F E)} (hz : z ∈ K1 hc n ST SG) (P : HeightOneSpectrum (𝓞 E)) (i j : Fin n) :
    Valued.v (adAt F P ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ≤ 1 := by
  obtain ⟨y, hy, -⟩ := St_one_int (congruence_subgroup_le_stabilizer hc n ST (principal_le_congruence_subgroup hc n ST SG hz))
  rw [hy]
  exact (mem_rInt_iff F E _).1 (y i j).2 P

theorem rhoP_mem_qbK {z : GL (Fin n) (AfE F E)} (hz : z ∈ K1 hc n ST SG) (P : HeightOneSpectrum (𝓞 E)) {c : E} (h0 : c ≠ 0)
    (hs : Sm Valued.v (P.valuation E c) (locM P z - 1)) : rhoP F P z ∈ qbK (algebraMap E (P.adicCompletion E) c) := by
  have hc0 : algebraMap E (P.adicCompletion E) c ≠ 0 := by
    simpa using h0
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · exact valuation_entries_le_one_of_mem_levelGroupOne hz P i j
  · rw [← map_inv]
    exact valuation_entries_le_one_of_mem_levelGroupOne (inv_mem hz) P i j
  · refine ⟨(locM P z - 1) i j / algebraMap E (P.adicCompletion E) c, ?_, ?_⟩
    · show Valued.v ((locM P z - 1) i j / algebraMap E (P.adicCompletion E) c) ≤ 1
      rw [map_div₀, valued_algebraMap]
      exact div_le_one_of_le₀ (hs i j) zero_le'
    · rw [mul_div_cancel₀ _ hc0]
      rfl

theorem topU_dense {U : Subgroup (GL (Fin n) (AfE F E))} {Λ : LevFam E K n SG} {Θ : LevQFam E K n Q} {d : Q → E} {k t : GL (Fin n) (AfE F E)}
    (e : ℕ) (hd : ∀ P, d P ≠ 0) (hQ : ∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q)
    (hdq : ∀ P : Q, d P = ((qOf P.1 : ℕ) : E) ^ e) (hk : k ∈ UAd hc n) (hrk : ∀ P : Q, rhoP F P.1 k = 1) (ht : t ∈ K1 hc n ST SG)
    (hU : ∀ x ∈ UAd hc n, x ∈ U ↔ k⁻¹ * x * k ∈ levU hc n ST SG Λ.grp) :
    ∀ g ∈ UAd hc n, ∃ x ∈ topU U t Θ d, ∃ p : DecoF E n ST SG Q, IsPtOf hc (g * x * (k * t)) p := by
  intro g hg
  have hkt : k * t ∈ UAd hc n := mul_mem hk (principal_le_adelic_unitary hc n ST SG ht)
  obtain ⟨z, hz, hsm, p, hp⟩ := _root_.GlobalTheory.Mem.ColAd.exists_K1_isPtOf F E hc n ST SG Q hQ (g * (k * t)) (mul_mem hg hkt) e
  have hzU := principal_le_adelic_unitary hc n ST SG hz
  refine ⟨(k * t) * z * (k * t)⁻¹, ?_, p, ?_⟩
  change (k * t) * z * (k * t)⁻¹ ∈ U ∧ _
  constructor
  · refine (hU _ (mul_mem (mul_mem hkt hzU) (inv_mem hkt))).2 ?_
    have e1 : k⁻¹ * ((k * t) * z * (k * t)⁻¹) * k = t * z * t⁻¹ := by group
    rw [e1]
    have hle := kOne_le_unipotentLevel hc n ST SG Λ.grp
    exact mul_mem (mul_mem (hle ht) (hle hz)) (inv_mem (hle ht))
  · refine Subgroup.mem_iInf.2 fun P => ?_
    have e2 : rhoT F P.1 t ((k * t) * z * (k * t)⁻¹) = rhoP F P.1 z := by
      have e3 : t⁻¹ * ((k * t) * z * (k * t)⁻¹) * t⁻¹⁻¹ = t⁻¹ * k * t * z * t⁻¹ * k⁻¹ * t := by group
      show rhoP F P.1 (t⁻¹ * ((k * t) * z * (k * t)⁻¹) * t⁻¹⁻¹) = _
      rw [e3]
      simp only [map_mul, map_inv, hrk P, inv_one, mul_one, inv_mul_cancel, one_mul, mul_inv_cancel_right]
      group
    refine Subgroup.mem_comap.2 ?_
    rw [e2]
    refine qbK_le_locLev P.1 (Θ P) (d P) (rhoP_mem_qbK hz P.1 (hd P) ?_)
    rw [hdq P]
    exact hsm P
  · have e4 : g * ((k * t) * z * (k * t)⁻¹) * (k * t) = g * (k * t) * z := by group
    rw [e4]
    exact hp

end Dense


set_option maxHeartbeats 1000000 in
theorem exists_clsG_top : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E hc.sig J T f bad) (Qv : Finset (HeightOneSpectrum (𝓞 F))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (e : ℕ) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (k t : GL (Fin n) (AfE F E)) (C : Type) (s : C → DecoF E n ST SG Q) (y : C → GL (Fin n) (AfE F E)) (stab : C → Type) [∀ c, Group (stab c)] (lat : C → Submodule (𝓞 E) (Fin n → E)) (gm : ∀ c, stab c →* UF E n) (ψ : topU S.U t Θ d →* ℂˣ), J = 1 → (∀ v, v ∈ Qv ↔ ∃ P ∈ Q, P.under (𝓞 F) = v) → (∀ v ∈ Qv, (T : 𝓞 F) ∉ v.asIdeal) → (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → (∀ P : Q, d P = ((qOf P.1 : ℕ) : E) ^ e) → k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ x ∈ UAd hc n, x ∈ S.U ↔ k⁻¹ * x * k ∈ levU hc n ST SG Λ.grp) → (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb ↔ (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) → (∀ c, IsPtOf hc (y c * (k * t)) (s c)) → (∀ c c' (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = s c' → c = c') → (∀ p, ∃ c, ∃ (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = p) → (∀ c, lat c = (s c).deco.1.L) → (∀ c, Function.Injective (gm c)) → (∀ c (γ : UF E n), γ ∈ (gm c).range ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = s c) → (∀ x : topU S.U t Θ d, (∀ P : Q, rhoP F P.1 x.1 = 1) → ψ x = 1) → ∃ C' : ClsG hc.sig J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F)))) stab lat, C'.lev.Lb = S.Lb ∧ C'.lev.U = topU S.U t Θ d ∧ (∀ v, v ∉ Qv → C'.lev.Uloc v = S.Uloc v) ∧ (∀ (x : C'.lev.U) (x' : S.U) (x'' : topU S.U t Θ d), x.1 = x'.1 → x.1 = x''.1 → C'.lev.chi x = S.chi x' * ψ x'') ∧ (∀ c, (C'.y c).1 = y c) ∧ ∀ c s, (C'.stabI c s).1 = ufGL E n (gm c s) := by
  intro F E K _ _ _ _ _ _ _ hc n _ ST SG Q J T f bad S Qv Λ Θ e d hd N hdN hΘ k t C s y stab _ lat gm ψ
    hJ hQv hT hQ hdq hk hrk ht hU hlatS hpt hinj hsurj hlatc hgmi hgr hψ
  subst hJ
  have hkt : k * t ∈ UAd hc n := mul_mem hk (principal_le_adelic_unitary hc n ST SG ht)
  have hover : ∀ P : Q, P.1.under (𝓞 F) ∈ Qv := fun P => (hQv _).2 ⟨P.1, P.2, rfl⟩
  have hloc : ∀ x ∈ S.U, (∀ v ∈ Qv, ∃ x' ∈ topU S.U t Θ d, bc (prV (E := E) v) x = bc (prV (E := E) v) x') → x ∈ topU S.U t Θ d := by
    intro x hx h
    refine ⟨hx, Subgroup.mem_iInf.2 fun P => ?_⟩
    obtain ⟨x', hx', e'⟩ := h _ (hover P)
    have e1 : rhoT F P.1 t x = rhoT F P.1 t x' := by
      show rhoP F P.1 (t⁻¹ * x * t⁻¹⁻¹) = rhoP F P.1 (t⁻¹ * x' * t⁻¹⁻¹)
      have e0 := localComponent_congr (P := P.1) rfl e'
      simp only [map_mul, e0]
    refine Subgroup.mem_comap.2 ?_
    rw [e1]
    exact rhoT_mem hx' P
  have hψ' : ∀ x : topU S.U t Θ d, (∀ v ∈ Qv, bc (prV (E := E) v) x.1 = 1) → ψ x = 1 := fun x h => hψ x fun P => by
    have h1 := localComponent_congr (P := P.1) rfl ((h _ (hover P)).trans (map_one (bc (prV (E := E) (P.1.under (𝓞 F))))).symm)
    rw [h1, map_one]
  obtain ⟨L, hLb, hLU, hLoc, hLchi⟩ := GlobalTheory.T.exists_stepLevel_smaller_at_finite_places F E hc.sig n 1 T f bad S Qv (topU S.U t Θ d) ψ (topU_le _ _ _ _) hT hloc
    (topU_open F E K hc.sig n 1 Q S.U t Θ d hd S.U_open) hψ'
  have hyU : ∀ c, y c ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) := fun c => by
    have h1 : y c * (k * t) * (k * t)⁻¹ ∈ UAd hc n := mul_mem (hpt c).uni (inv_mem hkt)
    rwa [mul_inv_cancel_right] at h1
  have hlev : ∀ (g x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), IsPtOf hc (g * (k * t)) p → IsPtOf hc (g * x * (k * t)) p' →
      (x ∈ topU S.U t Θ d ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p = p') :=
    fun g x p p' h h' => GlobalTheory.T.mem_framedLevel_iff_two_adelic_points F E K hc n ST SG Q Λ Θ d hd N hdN hΘ S.U k t g x p p' hk hrk ht hU h h'
  have hle : topU S.U t Θ d ≤ UAd hc n := fun x hx => ((S.U_eq x).1 (topU_le _ _ _ _ hx)).1
  let sI : ∀ c, stab c →* UJ (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) := fun c =>
    ((ufGL E n).comp (gm c)).codRestrict _ fun a => by
      show ufGL E n (gm c a) ∈ URat hc n
      rw [RatMove.ufGL_eq hc]
      exact ((ratEquiv hc n).symm (gm c a)).2
  refine ⟨{ lev := L, y := fun c => ⟨y c, hyU c⟩, y_bij := ?_, y_lat := ?_, stabI := sI, stabI_inj := ?_, stabI_range := ?_ },
    hLb, hLU, hLoc, hLchi, fun c => rfl, fun c a => rfl⟩
  · refine GlobalTheory.T.decoratedPointClasses_bijective_doubleCosets F E K hc n ST SG Q C Λ Θ s L.U (k * t) (fun c => ⟨y c, hyU c⟩) (hLU ▸ hle) hkt ?_ ?_ hpt hinj hsurj
    · rw [hLU]; exact hlev
    · rw [hLU]; exact topU_dense e hd hQ hdq hk hrk ht hU
  · intro c x
    rw [hlatc c, hLb]
    exact PtLat.latS_deco_iff F E hc n ST SG Q S.Lb k t (y c) (s c) ht hlatS (hpt c) x
  · intro c a b h
    have h1 : ufGL E n (gm c a) = ufGL E n (gm c b) := congrArg Subtype.val h
    exact hgmi c (Subtype.ext ((toGLm E n).injective h1))
  · intro c γ
    have e1 : ufGL E n (ratHom hc n γ) = γ.1 := by
      rw [RatMove.ufGL_eq hc]
      exact congrArg Subtype.val ((ratEquiv hc n).symm_apply_apply γ)
    have key := stab_iff_mem_conj F E K hc n ST SG Q Λ Θ (topU S.U t Θ d) (k * t) (y c) (s c) hlev (hpt c) (ratHom hc n γ)
    have e2 : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 = ratAd F (ratHom hc n γ) := by rw [ratAd, e1]
    rw [e2, hLU]
    refine Iff.trans ?_ ((hgr c _).trans key)
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, Subtype.ext ((toGLm E n).injective ?_)⟩
      exact (congrArg Subtype.val ha).trans e1.symm
    · rintro ⟨a, ha⟩
      refine ⟨a, Subtype.ext ?_⟩
      show ufGL E n (gm c a) = γ.1
      rw [ha, e1]

end GlobalTheory.Mem.Col2.TopCh

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReferenceClassMatchingCouplingCoset
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match

theorem mem_image_units {κ : Type} [CommRing κ] {n : ℕ} (C : Set (Fin n → κ)) (y : GL (Fin n) κ) (w : Fin n → κ) :
    w ∈ (fun v => y.1 *ᵥ v) '' C ↔ (y⁻¹).1 *ᵥ w ∈ C := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  · intro h
    refine ⟨_, h, ?_⟩
    show y.1 *ᵥ ((y⁻¹).1 *ᵥ w) = w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem conj_mem_setStab_image {κ : Type} [CommRing κ] {n : ℕ} (C : Set (Fin n → κ)) (y h : GL (Fin n) κ) :
    y * h * y⁻¹ ∈ MemChart.setStab ((fun v => y.1 *ᵥ v) '' C) ↔ h ∈ MemChart.setStab C := by
  have e1 : ∀ w : Fin n → κ, (y⁻¹).1 *ᵥ ((y * h * y⁻¹).1 *ᵥ w) = h.1 *ᵥ ((y⁻¹).1 *ᵥ w) := fun w => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, show y⁻¹ * (y * h * y⁻¹) = h * y⁻¹ by group, Units.val_mul, ← Matrix.mulVec_mulVec]
  have e2 : ∀ v : Fin n → κ, (y⁻¹).1 *ᵥ (y.1 *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  show (∀ w, (y * h * y⁻¹).1 *ᵥ w ∈ (fun v => y.1 *ᵥ v) '' C ↔ w ∈ (fun v => y.1 *ᵥ v) '' C) ↔ ∀ v, h.1 *ᵥ v ∈ C ↔ v ∈ C
  simp only [mem_image_units, e1]
  constructor
  · intro H v
    have := H (y.1 *ᵥ v)
    rwa [e2] at this
  · intro H w
    exact H _


set_option maxHeartbeats 1000000 in
theorem coset_match : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ), 1 ≤ i → i < B.R.m →
    ∀ (c : (I.stp u a i).Cl) (b0 : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) i), ∃ c0 : (I.stp u I.mu0 i).Cl, c0.1 = b0 ∧
      ∃ y : GLG (E := B.fields.E) (n := B.R.N i) (SG := (B.primes X).vGs), y ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).grp ∧
      ∀ (κ : (I.stp u a i).G c.1) (κ0 : (I.stp u I.mu0 i).G c0.1), (I.stp u a i).gam c.1 κ = 1 → (I.stp u I.mu0 i).gam c0.1 κ0 = 1 →
        κ.2.2 = 1 → (i + 1 = B.R.m → ∀ w, κ0.2.1.1 w = y w * κ.2.1.1 w * (y w)⁻¹) →
        (cosetIn ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)) = cosetIn ((I.stp u a i).rep c) ↔
          cosetIn ((I.stp u I.mu0 i).act c0.1 κ0 ((I.stp u I.mu0 i).rep c0)) = cosetIn ((I.stp u I.mu0 i).rep c0)) := by
  intro B X I hI l u a i h1 hm c b0
  classical
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  by_cases hl : i + 1 = B.R.m
  · have hq : ∀ w ∈ (B.primes X).vGs, ((qOf w : ℕ) : 𝓞 B.fields.E) ∉ w.asIdeal ^ 2 :=
      fun _ hw => GlobalTheory.TopStep.qOf_notMem_sq (GlobalTheory.Mem.FieldsLaws.fields_ok B) l.pr hw
    set r : PtAt B.R I.sel (I.tup a) (I.cst a) u i := (I.stp u a i).rep c with hr
    obtain ⟨y, hy, hy0, hY⟩ := ChEx.ptAt_cosetG r hl
    have hGs : ∀ P : rowSG (B.primes X) I.sel (I.tup I.mu0), P.1 ∈ (B.primes X).vGs := fun P => by
      rcases Finset.mem_union.1 P.2 with h | h
      · exact h
      · have h' : P.1 ∈ I.Q I.mu0 := h
        rw [I.twistPrimes_reference_tuple_eq_empty] at h'
        exact absurd h' (Finset.notMem_empty _)
    let Y0 : Set (Sp B.fields.E (B.R.N i)) := {z | z - y ∈ locLat (rowSG (B.primes X) I.sel (I.tup I.mu0)) r.1.1.deco.1.N
        (fun P => if P.1 ∈ (B.primes X).vGs then 0 else ((I.cst I.mu0).M : ℤ))}
    have hY0 : Y0 ∈ (ysAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) i).ys
        (extTo (QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K)) r.1.1).deco.1.N := by
      rw [ysAt_ys_of_eq _ _ _ hl]
      refine ⟨y, (mem_locLat _ _ _ _).2 fun P => ?_, rfl⟩
      rw [if_pos (hGs P), _root_.zpow_neg_one, inv_inv]
      exact hy P.1 (hGs P)
    let q0 : PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u i := ⟨(extTo _ r.1.1, Y0), hY0⟩
    have hbar : MemChart.bar q0 = MemChart.bar r := by
      funext w
      have hy' : ∀ w ∈ (B.primes X).vGs, ((qOf w : ℕ) : B.fields.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q0.1.1.deco.1.N := hy
      have hy0' : y ∈ q0.1.2 := by
        change y - y ∈ locLat (rowSG (B.primes X) I.sel (I.tup I.mu0)) r.1.1.deco.1.N
          (fun P => if P.1 ∈ (B.primes X).vGs then 0 else ((I.cst I.mu0).M : ℤ))
        rw [sub_self]
        exact zero_mem _
      have hY' : ∀ z ∈ q0.1.2, ∀ w ∈ (B.primes X).vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q0.1.1.deco.1.N := by
        intro z hz w hw
        have h2 := (mem_locLat _ _ _ _).1 hz ⟨w, Finset.mem_union_left _ hw⟩
        exact (by simpa [hw] using h2 : z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal r.1.1.deco.1.N)
      rw [ChEx.bar_eqG q0 hy' hy0' hY' w, ChEx.bar_eqG r hy hy0 hY w]
      rfl
    refine ⟨(I.stp u I.mu0 i).cl b0 q0, rfl, ?_⟩
    obtain ⟨g0, hg0⟩ := (I.stp u I.mu0 i).exists_mv b0 q0
    refine ⟨(g0.2.1.1)⁻¹, inv_mem g0.2.1.2, ?_⟩
    intro κ κ0 _ _ hθ hκ
    have hκ' := hκ hl
    set r0 : PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u i := (I.stp u I.mu0 i).rep ((I.stp u I.mu0 i).cl b0 q0) with hr0
    have hb0 : ∀ w, MemChart.bar q0 w = (fun v => (g0.2.1.1 w).1 *ᵥ v) '' MemChart.bar r0 w := by
      intro w
      have e : MemChart.ya (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0)
          (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0) g0 r0 = q0 := hg0
      have h3 := MemChart.bar_ya (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0)
          (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0) g0 r0 w
      rw [e] at h3
      exact h3
    have hb0' : ∀ w, MemChart.bar r0 w = (fun v => (((g0.2.1.1)⁻¹ : GLG (E := B.fields.E) (n := B.R.N i) (SG := (B.primes X).vGs)) w).1 *ᵥ v) '' MemChart.bar r w := by
      intro w
      have e : ∀ v, ((g0.2.1.1 w)⁻¹).1 *ᵥ ((g0.2.1.1 w).1 *ᵥ v) = v := fun v => by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rw [← hbar, hb0 w, Set.image_image]
      show MemChart.bar r0 w = (fun v => ((g0.2.1.1 w)⁻¹).1 *ᵥ ((g0.2.1.1 w).1 *ᵥ v)) '' MemChart.bar r0 w
      simp only [e, Set.image_id']
    have hL : cosetIn ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)) = cosetIn ((I.stp u a i).rep c) ↔
        ∀ w, κ.2.1.1 w ∈ MemChart.setStab (MemChart.bar r w) := by
      show cosetIn (MemChart.ya (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1)
          (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1) κ r) = cosetIn r ↔ _
      rw [ChEx.cosetIn_eq_iff_bar_cq (ChEx.q_disj I hI a) hq, MemChart.bar_ya_eq_iff]
      have hcq : ChEx.cqOf (MemChart.ya (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1)
          (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1) κ r) = ChEx.cqOf r := by
        funext P
        rw [ChEx.invActs_cqOf (ChEx.q_disj I hI a) _ _ κ r P, hθ]
        ext v
        simp
      rw [hcq]
      simp
    have hR : cosetIn ((I.stp u I.mu0 i).act ((I.stp u I.mu0 i).cl b0 q0).1 κ0 r0) = cosetIn r0 ↔
        ∀ w, κ0.2.1.1 w ∈ MemChart.setStab (MemChart.bar r0 w) := by
      show cosetIn (MemChart.ya (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0)
          (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0) κ0 r0) = cosetIn r0 ↔ _
      rw [ChEx.cosetIn_eq_iff_bar_cq (ChEx.q_disj I hI I.mu0) hq, MemChart.bar_ya_eq_iff]
      have hcq : ChEx.cqOf (MemChart.ya (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0)
          (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0) κ0 r0) = ChEx.cqOf r0 := by
        funext P
        have h' : P.1 ∈ I.Q I.mu0 := P.2
        rw [I.twistPrimes_reference_tuple_eq_empty] at h'
        exact absurd h' (Finset.notMem_empty _)
      rw [hcq]
      simp
    rw [hL, hR]
    refine forall_congr' fun w => ?_
    rw [hκ' w, hb0' w]
    exact (conj_mem_setStab_image _ _ _).symm
  · let q0 : PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u i :=
      ⟨(DecoF.base _ _ _ _ _, ∅), by rw [ysAt_ys_of_ne I.sel (I.tup I.mu0) (I.cst I.mu0) hl]; rfl⟩
    refine ⟨(I.stp u I.mu0 i).cl b0 q0, rfl, 1, one_mem _, fun κ κ0 _ _ _ _ => ?_⟩
    exact iff_of_true (ChEx.cos_of_neT I hl _ _) (ChEx.cos_of_neT I hl _ _)

end GlobalTheory.Mem.Col2.TC.ChTw.Match
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepLevelConjBaseLatticeUnitaryStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stepLevel_conj_baseLatticeUnitary : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (b : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), b ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → (∀ v, bc (prV (E := E) v) b ∈ levelVL σ J v S.Lb) → (∀ v, (T : 𝓞 F) ∈ v.asIdeal → (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = S.Uloc v) → (∀ v, v ∉ bad → (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) b = 1) → ∃ S' : StepLevel F E σ J T f bad, S'.Lb = S.Lb ∧ S'.U = S.U.map (MulAut.conj b).toMonoidHom ∧ ∀ (x : S'.U) (z : S.U), x.1 = b * z.1 * b⁻¹ → S'.chi x = S.chi z := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.exists_stepLevel_conj | exact GlobalTheory.Mem.Col2.ChEx.exists_stepLevel_conj | (intros; apply GlobalTheory.Mem.Col2.ChEx.exists_stepLevel_conj <;> assumption)
end

