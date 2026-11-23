module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.OrthXflagMaps

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyMSLeaf
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S IsDedekindDomain Function

namespace Formalism.L2.SG.Pf.Carrier.EnergyMS

open Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def StepGSplit : Prop := ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), GSplitX X

def TypCount : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (i : Fin 2),
    (Finset.univ.filter (fun p : TypX X => gAt X p.1 = D.host.g i)).card = D.R.f

theorem typNorm_of (hG : StepGSplit) (hC : TypCount) : TypNorm := by
  intro D X
  have hgA : ∀ p : TypX X, ((Ideal.absNorm p.1.asIdeal : ℕ) : ℝ) = ((gAt X p.1 : ℕ) : ℝ) := fun p => by
    rw [(hG D X p).1]
  simp only [hgA]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun p : TypX X => gAt X p.1 = D.host.g 0)]
  have h0 : ∀ p ∈ Finset.univ.filter (fun p : TypX X => gAt X p.1 = D.host.g 0),
      ((gAt X p.1 : ℕ) : ℝ) = ((D.host.g 0 : ℕ) : ℝ) := fun p hp => by
    rw [(Finset.mem_filter.1 hp).2]
  have h1 : ∀ p ∈ Finset.univ.filter (fun p : TypX X => ¬ gAt X p.1 = D.host.g 0),
      ((gAt X p.1 : ℕ) : ℝ) = ((D.host.g 1 : ℕ) : ℝ) := fun p hp => by
    have h := (Finset.mem_filter.1 hp).2
    unfold gAt at h ⊢
    split_ifs at h ⊢ with hg
    · exact absurd rfl h
    · rfl
  rw [Finset.prod_congr rfl h0, Finset.prod_congr rfl h1, Finset.prod_const, Finset.prod_const]
  have hc1 : Finset.univ.filter (fun p : TypX X => ¬ gAt X p.1 = D.host.g 0) =
      Finset.univ.filter (fun p : TypX X => gAt X p.1 = D.host.g 1) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold gAt
    have hne := D.host.g_ne
    split_ifs <;> simp [hne, Ne.symm hne]
  rw [hc1, hC D X 0, hC D X 1, Formalism.MainNotions.S.Lat.gS, Nat.cast_mul, mul_pow]

theorem dN_eq {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : PlX X) :
    dN X v = ((Nat.castRingHom ℝ : ℕ →* ℝ).comp (Ideal.absNorm : Ideal (𝓞 X.B.I.F) →*₀ ℕ).toMonoidHom)
      (v.maxPowDividing (differentIdeal ℤ (𝓞 X.B.I.F))) := rfl

theorem diffProd_holds : DiffProd := by
  intro D X
  have hne : differentIdeal ℤ (𝓞 X.B.I.F) ≠ ⊥ := by
    intro h
    have h2 := NumberField.absNorm_differentIdeal (K := X.B.I.F) (𝓞 X.B.I.F)
    rw [h, Ideal.absNorm_bot] at h2
    exact NumberField.discr_ne_zero X.B.I.F (Int.natAbs_eq_zero.mp h2.symm)
  have hfin := Ideal.hasFiniteMulSupport hne
  have hdN : dN X = fun v => ((Nat.castRingHom ℝ : ℕ →* ℝ).comp
      (Ideal.absNorm : Ideal (𝓞 X.B.I.F) →*₀ ℕ).toMonoidHom) (v.maxPowDividing (differentIdeal ℤ (𝓞 X.B.I.F))) :=
    funext (fun v => dN_eq X v)
  refine ⟨?_, ?_⟩
  · rw [hdN]
    exact hfin.subset (Function.mulSupport_comp_subset (map_one _) _)
  · rw [hdN, ← MonoidHom.map_finprod _ hfin, Ideal.finprod_heightOneSpectrum_factorization hne]
    show ((Ideal.absNorm (differentIdeal ℤ (𝓞 X.B.I.F)) : ℕ) : ℝ) = _
    rw [NumberField.absNorm_differentIdeal (K := X.B.I.F) (𝓞 X.B.I.F), Nat.cast_natAbs, Int.cast_abs]

def DiscEF : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D),
    |((NumberField.discr X.B.I.E : ℤ) : ℝ)| = |((NumberField.discr X.B.I.F : ℤ) : ℝ)| ^ 2

def DegE : Prop := ∀ (D : D7), Module.finrank ℚ D.host.E = 2 * D.R.f

theorem discRd_of (hE : DiscEF) (hd : DegE) : DiscRd := by
  intro D X
  have hdisc : NumberField.discr X.B.I.E = NumberField.discr D.host.E :=
    NumberField.discr_eq_discr_of_algEquiv (K := X.B.I.E) X.ιE.toRatAlgEquiv
  have h1 := hE D X
  rw [hdisc] at h1
  have h2 := hd D
  have ha : 0 ≤ |((NumberField.discr X.B.I.F : ℤ) : ℝ)| := abs_nonneg _
  have hpos : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
  have hf : (D.R.f : ℝ) ≠ 0 := by
    have : D.R.f ≠ 0 := by omega
    exact_mod_cast this
  unfold Formalism.BasicNotions.Host.rdE
  rw [h1, h2, ← Real.rpow_natCast (|((NumberField.discr X.B.I.F : ℤ) : ℝ)|) 2, ← Real.rpow_mul ha,
    ← Real.rpow_natCast _ D.R.f, ← Real.rpow_mul ha]
  have hex : ((2 : ℕ) : ℝ) * (1 / ((2 * D.R.f : ℕ) : ℝ)) * (D.R.f : ℝ) = 1 := by
    push_cast
    field_simp
  rw [hex, Real.rpow_one]

theorem lemmaMSStd_of_leaves (hO : MSOrd) (hT : MSTyp) (hG : StepGSplit) (hC : TypCount) (hE : DiscEF) (hd : DegE)
    {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : Formalism.L2.SG.Pf.Carrier.EnergyConst2.LemmaMSStd X u u' ψ := by
  exact lemmaMSStd_of hO hT diffProd_holds (discRd_of hE hd) (typNorm_of hG hC) X u u' ψ

end Formalism.L2.SG.Pf.Carrier.EnergyMS
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXJoint
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
  {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def JointTensorAt (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v)
    (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)),
    ptOfL (D := D) (D.R.rS + 1) p = some w → (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h' →
    ∀ x : ∀ v, X.Vloc u' v,
      (X.piU u h⁻¹) ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
        Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w))
          (X.piU u' h' (X.tensU u' x))) =
        X.tensU u (fun v => eP v
          (((((Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG (S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
              (Formalism.FourierDecayAlt.C.loc (S.emb (τ.symm v)) p))⁻¹ : ℝ) : ℂ) •
            Formalism.FourierDecayAlt.D.vecV (T (τ.symm v)).base (ν' (τ.symm v)) (m₀ (τ.symm v)) (f (τ.symm v))
              (Formalism.FourierDecayAlt.D.toStd S.G.r S.g 1 (Formalism.FourierDecayAlt.C.loc (S.emb (τ.symm v)) p)))
            ((eQ v).symm (x v))))

theorem vJoint_of_tensorAt (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v)
    (sc : ℝ) (hsc : 0 < sc) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (hi : ∀ v, i0 v = i0' v)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (h2 : JointTensorAt X u u' S T f ν' m₀ τ eP eQ sc i0 i0' νq) :
    VJoint X S u u' sc i0 i0' νq T f ν' m₀ τ eP eQ := by
  unfold JointTensorAt at h2
  unfold VJoint
  intro p w hpw hrep hpos x
  have hex : ∃ q : X.B.I.Ginf × X.B.I.Ginf, IsDFrameX X u u' sc i0 i0' (gamW X u u' w) q.1 q.2 := by
    have hii : i0' = i0 := funext fun v => (hi v).symm
    rw [hii]
    obtain ⟨h, h', hh⟩ := dual_frame_at_places X u u' sc i0 hsc w hrep hpos
    exact ⟨(h, h'), hh⟩
  refine Eq.trans ?_ (h2 p w hpw hrep hpos hex.choose.1 hex.choose.2 hex.choose_spec x)
  unfold unscaledOperatorAtPointRepresentative unscaledFrameConjugatedOperator
  rw [if_pos hrep, dite_eq_left hex]
  rfl

private theorem sign_flip_involutive {K : Type} [Ring K] (r b : ℕ) (x : Formalism.FourierDecayAlt.TB.Pt K) :
    Formalism.L2.SG.DataInst.signAux r b (Formalism.L2.SG.DataInst.signAux r b x) = x := by
  induction x generalizing b with
  | nil => rfl
  | cons a rest ih =>
    obtain ⟨s, t⟩ := a
    have hm : ∀ n : ℕ, ((-1 : K) ^ n) * ((-1 : K) ^ n * t) = t := by
      intro n
      rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
    simp only [Formalism.L2.SG.DataInst.signAux, hm, ih]

private theorem exists_pt_ptOfL_of_point (w : Point D.host.E (D.R.rS + 1)) :
    ∃ p : Formalism.FourierDecayAlt.TB.Pt D.host.E, ptOfL (D := D) (D.R.rS + 1) p = some w := by
  refine ⟨Formalism.L2.SG.DataInst.signPt D.R.rS (Formalism.L2.S.ptList w), ?_⟩
  have hs : Formalism.L2.SG.DataInst.signPt D.R.rS (Formalism.L2.SG.DataInst.signPt D.R.rS (Formalism.L2.S.ptList w)) =
      Formalism.L2.S.ptList w := sign_flip_involutive _ _ _
  unfold ptOfL Formalism.L2.SG.DataInst.ptOfList
  split_ifs with h
  · congr 1
    rw [Equiv.symm_apply_eq]
    exact Subtype.ext hs
  · exact (h (by rw [hs]; exact Formalism.L2.S.ptList_isPtL w)).elim

theorem vIndepAt_of_tensorAt (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v)
    (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hJT : JointTensorAt X u u' S T f ν' m₀ τ eP eQ sc i0 i0' νq) : VIndepAt X u u' sc i0 i0' νq := by
  unfold JointTensorAt at hJT
  unfold VIndepAt
  intro w hrep hpos h₁ h₁' h₂ h₂' hf₁ hf₂
  obtain ⟨p, hp⟩ := exists_pt_ptOfL_of_point (D := D) w

  refine ContinuousLinearMap.coe_injective (LinearMap.ext_on_range (X.81 u') fun x => ?_)
  have e1 := hJT p w hp hrep hpos h₁ h₁' hf₁ x
  have e2 := hJT p w hp hrep hpos h₂ h₂' hf₂ x
  exact e1.trans e2.symm

end Formalism.L2.SG.Pf.CarrierXAll
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PerpIffOrth
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.Pf.FibreCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rel

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}

theorem grel_equiv : Equivalence (GRel X u u' F0 F0' Λ Λ') := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    exact ⟨1, Formalism.L2.SG.TermDef.one_mem_NLam _ _, 1, Formalism.L2.SG.TermDef.one_mem_NLam _ _, by simp⟩
  · rintro p q ⟨n, hn, n', hn', h⟩
    exact ⟨n⁻¹, Formalism.L2.SG.Pf.nlamPf_inv hn, n'⁻¹, Formalism.L2.SG.Pf.nlamPf_inv hn', by rw [h]; group⟩
  · rintro p q w ⟨n, hn, n', hn', h⟩ ⟨m, hm, m', hm', h'⟩
    exact ⟨m * n, Formalism.L2.SG.Pf.nlamPf_mul hm hn, n' * m', Formalism.L2.SG.Pf.nlamPf_mul hn' hm', by rw [h', h]; group⟩

theorem lin_of_cls {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (s : GTerm X u u' F0 F0' what₂ rows')
    (p : GCar X u u' F0 F0' s.lam s.lam') (h : s.cls = Quot.mk _ p) :
    ∃ n ∈ NLam s.lam (lf D F0), ∃ n' ∈ NLam s.lam' (lf D F0'), s.lin = n * p.1.2 * n' := by
  have e : Quot.mk (GRel X u u' F0 F0' s.lam s.lam') p = Quot.mk _ (Quot.out s.cls) :=
    h.symm.trans (Quot.out_eq _).symm
  exact grel_equiv.eqvGen_iff.1 (Quot.eqvGen_exact e)

end Rel

section WD

variable {D : D7} {T T' : D.host.E} {F : FlagG (VS D) D.R.rS T} (F0' : FlagG (VS D) D.R.rS T')

theorem perp_iff_orth {y : (VS D).V} : y ∈ perpS (VS D) F0'.X ↔ y ∈ orth (VS D) (Xsp (lf D F0')) := by
  rw [Formalism.L2.SG.Pf.mem_orth_iff_td]; rfl

variable {F0'}

theorem nlam_X {Λ₀ : Submodule (𝓞 D.host.E) (VS D).V} {ν : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hν : ν ∈ NLam Λ₀ (lf D F0')) : ∀ y ∈ F0'.X, ν y ∈ F0'.X := by
  intro y hy
  have h := Formalism.L2.SG.Pf.nlam_mapsTo hν D.R.rS y (by rw [Formalism.L2.SG.Pf.xflag_r]; exact hy)
  rwa [Formalism.L2.SG.Pf.xflag_r] at h

theorem nlam_P {Λ₀ : Submodule (𝓞 D.host.E) (VS D).V} {ν : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hν : ν ∈ NLam Λ₀ (lf D F0')) : ∀ y ∈ perpS (VS D) F0'.X, ν y ∈ perpS (VS D) F0'.X := by
  intro y hy
  rw [perp_iff_orth] at hy ⊢
  exact Formalism.L2.SG.Pf.nlam_orth_mapsTo hν y hy

theorem nlam_triv {Λ₀ : Submodule (𝓞 D.host.E) (VS D).V} {ν : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hν : ν ∈ NLam Λ₀ (lf D F0')) : ∀ y ∈ perpS (VS D) F0'.X, ν y - y ∈ F0'.X :=
  fun y hy => hν.2.2 y ((perp_iff_orth F0').1 hy)

theorem indL_zero (f : (VS D).V →ₗ[D.host.E] (VS D).V) (hP : ∀ y ∈ perpS (VS D) F0'.X, f y ∈ perpS (VS D) F0'.X)
    (hX : ∀ y ∈ F0'.X, f y ∈ F0'.X) (h : ∀ y, f y = 0) : indL F0' f hP hX = 0 := by
  refine LinearMap.ext fun w => ?_
  induction w using Submodule.Quotient.induction_on with
  | H x =>
    rw [indL_mk, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
    show f x ∈ F0'.X
    rw [h]; exact zero_mem _

theorem wd {Λ Λ₀ : Submodule (𝓞 D.host.E) (VS D).V} {γ₀ n n' ν ν' c c' : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NLam Λ (lf D F)) (hn' : n' ∈ NLam Λ (lf D F))
    (hν : ν ∈ NLam Λ₀ (lf D F0')) (hν' : ν' ∈ NLam Λ₀ (lf D F0'))
    (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hc' : c' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hg : Formalism.HermitianLatticesTheory.gmap c Λ₀ = Λ₀) (hg' : Formalism.HermitianLatticesTheory.gmap c' Λ₀ = Λ₀)
    (hfix : ∀ a, c (F0'.fvec a) = F0'.fvec a) (hfix' : ∀ a, c' (F0'.fvec a) = F0'.fvec a)
    (he : n * γ₀ * ν * c = n' * γ₀ * ν' * c') [Finite (autLz D F0' Λ₀)] :
    ∀ y ∈ perpS (VS D) F0'.X, c y - c' y ∈ F0'.X := by
  set d := c' * c⁻¹ with hddef
  have hd : d ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := Subgroup.mul_mem _ hc' (Subgroup.inv_mem _ hc)
  have hdfix : ∀ a, d (F0'.fvec a) = F0'.fvec a := by
    intro a; show c' (c⁻¹ _) = _; rw [inv_fix F0' hfix a, hfix' a]
  have hdg : Formalism.HermitianLatticesTheory.gmap d Λ₀ = Λ₀ := by
    rw [hddef, Formalism.L2.SG.Pf.gmap_mul_sat, gmap_inv_of hg, hg']
  set g := γ₀⁻¹ * (n'⁻¹ * n) * γ₀ with hgdef
  have hgd : g = ν' * d * ν⁻¹ := by
    calc g = γ₀⁻¹ * n'⁻¹ * (n * γ₀ * ν * c) * c⁻¹ * ν⁻¹ := by rw [hgdef]; group
      _ = γ₀⁻¹ * n'⁻¹ * (n' * γ₀ * ν' * c') * c⁻¹ * ν⁻¹ := by rw [he]
      _ = ν' * d * ν⁻¹ := by rw [hddef]; group
  have hnil : ((g : (VS D).V →ₗ[D.host.E] (VS D).V) - 1) ^ (2 * D.R.rS + 1) = 0 :=
    conj_nilp (Formalism.L2.SG.Pf.nlamPf_mul (Formalism.L2.SG.Pf.nlamPf_inv hn') hn) γ₀
  have hdP := perp_maps F0' hd hdfix
  have hdX : ∀ y ∈ F0'.X, d y ∈ F0'.X := fun y hy => by rw [fix_X F0' hdfix y hy]; exact hy
  have hνi := Formalism.L2.SG.Pf.nlamPf_inv hν
  have hgapp : ∀ y, g y = ν' (d (ν⁻¹ y)) := fun y => by rw [hgd]; rfl
  have hgP : ∀ y ∈ perpS (VS D) F0'.X, g y ∈ perpS (VS D) F0'.X := fun y hy => by
    rw [hgapp]; exact nlam_P hν' _ (hdP _ (nlam_P hνi _ hy))
  have hgX : ∀ y ∈ F0'.X, g y ∈ F0'.X := fun y hy => by
    rw [hgapp]; exact nlam_X hν' _ (hdX _ (nlam_X hνi _ hy))

  have hgdX : ∀ y ∈ perpS (VS D) F0'.X, g y - d y ∈ F0'.X := by
    intro y hy
    have ha := nlam_triv hνi y hy
    have e1 : d (ν⁻¹ y) = d y + (ν⁻¹ y - y) := by
      have : ν⁻¹ y = y + (ν⁻¹ y - y) := by abel
      conv_lhs => rw [this]
      rw [map_add (f := _), fix_X F0' hdfix _ ha]
    have e2 : g y - d y = (ν' (d y) - d y) + ν' (ν⁻¹ y - y) := by
      rw [hgapp, e1, map_add (f := _)]; abel
    rw [e2]
    exact add_mem (nlam_triv hν' _ (hdP y hy)) (nlam_X hν' _ ha)
  have hg1P : ∀ y ∈ perpS (VS D) F0'.X, ((g : (VS D).V →ₗ[D.host.E] (VS D).V) - 1) y ∈ perpS (VS D) F0'.X :=
    fun y hy => by
      rw [LinearMap.sub_apply, Module.End.one_apply]; exact sub_mem (hgP y hy) hy
  have hg1X : ∀ y ∈ F0'.X, ((g : (VS D).V →ₗ[D.host.E] (VS D).V) - 1) y ∈ F0'.X := fun y hy => by
    rw [LinearMap.sub_apply, Module.End.one_apply]; exact sub_mem (hgX y hy) hy
  set TD := indL F0' (d : (VS D).V →ₗ[D.host.E] (VS D).V) hdP hdX with hTD
  have hTD1 : TD - 1 = indL F0' ((g : (VS D).V →ₗ[D.host.E] (VS D).V) - 1) hg1P hg1X := by
    refine LinearMap.ext fun w => ?_
    induction w using Submodule.Quotient.induction_on with
    | H x =>
      rw [LinearMap.sub_apply, Module.End.one_apply, hTD, indL_mk, indL_mk, ← Submodule.Quotient.mk_sub,
        Submodule.Quotient.eq]
      show (d x - x) - (g x - x) ∈ F0'.X
      have : (d x - x) - (g x - x) = -(g x - d x) := by abel
      rw [this]
      exact neg_mem (hgdX x x.2)
  have hTDnil : (TD - 1) ^ (2 * D.R.rS + 1) = 0 := by
    rw [hTD1, indL_pow]
    exact indL_zero _ _ _ (fun y => by rw [hnil]; rfl)

  have hdpow : ∀ i : ℕ, d ^ i ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ a, (d ^ i) (F0'.fvec a) = F0'.fvec a) ∧
      Formalism.HermitianLatticesTheory.gmap (d ^ i) Λ₀ = Λ₀ := by
    intro i
    induction i with
    | zero => exact ⟨Subgroup.one_mem _, fun a => rfl, Formalism.L2.SG.Pf.gmap_one_sat _⟩
    | succ i ih =>
      refine ⟨by rw [pow_succ]; exact Subgroup.mul_mem _ ih.1 hd, fun a => ?_, ?_⟩
      · rw [pow_succ, LinearEquiv.mul_apply, hdfix, ih.2.1]
      · rw [pow_succ, Formalism.L2.SG.Pf.gmap_mul_sat, hdg, ih.2.2]
  have hTDpow : ∀ (i : ℕ) (x : perpS (VS D) F0'.X), (TD ^ i) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨(d ^ i) x, perp_maps F0' (hdpow i).1 (hdpow i).2.1 _ x.2⟩ := by
    intro i
    induction i with
    | zero => intro x; rfl
    | succ i ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, hTD, indL_mk, ← hTD, ih]
      rfl
  have hmem : ∀ i : ℕ, ⇑(TD ^ i) ∈ autLz D F0' Λ₀ := fun i =>
    ⟨d ^ i, stabF_of_fix F0' (hdpow i).1 (hdpow i).2.1, (hdpow i).2.2, fun x _ => hTDpow i x⟩
  obtain ⟨i, j, hij, hφ⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun i : ℕ => (⟨⇑(TD ^ i), hmem i⟩ : autLz D F0' Λ₀))
  have hpow : TD ^ i = TD ^ j := LinearMap.coe_injective (congrArg Subtype.val hφ)
  have hunit : IsUnit TD := by
    have hdiP := perp_maps F0' (Subgroup.inv_mem _ hd) (inv_fix F0' hdfix)
    have hdiX : ∀ y ∈ F0'.X, d⁻¹ y ∈ F0'.X := fun y hy => by rw [fix_X F0' (inv_fix F0' hdfix) y hy]; exact hy
    refine ⟨⟨TD, indL F0' ((d⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) hdiP hdiX,
      ?_, ?_⟩, rfl⟩ <;>
    · refine LinearMap.ext fun w => ?_
      induction w using Submodule.Quotient.induction_on with
      | H x =>
        rw [Module.End.mul_apply, hTD, indL_mk, indL_mk, Module.End.one_apply]
        congr 1
        apply Subtype.ext
        simp [LinearEquiv.coe_inv]
  have hfin : ∃ k, 0 < k ∧ TD ^ k = 1 := by
    rcases lt_or_gt_of_ne hij with h | h
    · refine ⟨j - i, by omega, ?_⟩
      have e : TD ^ i * TD ^ (j - i) = TD ^ i * 1 := by rw [← pow_add, Nat.add_sub_cancel' h.le, mul_one, hpow]
      exact (hunit.pow i).mul_left_cancel e
    · refine ⟨i - j, by omega, ?_⟩
      have e : TD ^ j * TD ^ (i - j) = TD ^ j * 1 := by rw [← pow_add, Nat.add_sub_cancel' h.le, mul_one, hpow]
      exact (hunit.pow j).mul_left_cancel e
  obtain ⟨k, hk, hk1⟩ := hfin
  have hTD : TD = 1 := unip_fin TD hk hk1 hTDnil
  intro y hy
  have hcy := perp_maps F0' hc hfix y hy
  have e := congrArg (fun A : Module.End D.host.E (WbQ D F0') => A (Submodule.Quotient.mk ⟨c y, hcy⟩)) hTD
  simp only [Module.End.one_apply] at e
  rw [indL_mk, Submodule.Quotient.eq] at e
  have e3 : c' y = (d : (VS D).V →ₗ[D.host.E] (VS D).V) (c y) := by
    rw [hddef]; simp [LinearEquiv.coe_inv]
  have h3 : c' y - c y ∈ F0'.X := by
    have := e
    simp only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub] at this
    rw [e3]; exact this
  rw [← neg_sub]
  exact neg_mem h3

end WD

end Formalism.L2.SG.Pf.FibreCounting
end
end

