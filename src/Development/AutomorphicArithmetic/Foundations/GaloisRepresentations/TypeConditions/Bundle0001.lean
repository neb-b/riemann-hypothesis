module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SemisimpleOfFin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0211
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.CuspOfCq
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleResidualTameEigenvalues
section
noncomputable section

namespace UpperTheory.GalS

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleThreePrime Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TypeLeaf (labSig FullLab)

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def LabTameS : Prop :=
  (∀ (k : Fin 2) (v : N.PlG k) (a : A.LP (A.plGw k v)), (A.items₂ k (A.plGw k v) a).natDegree = A.lpDim a →
    ∀ σ ∈ Ine (F := H.E) (N.plOm.1 (A.plGw k v)), σ ∈ wildSet N (N.plOm.1 (A.plGw k v)) →
      A.inePol a σ = (X - 1) ^ A.lpDim a) ∧
  ∀ (k : Fin 2) (v : N.PlG k) (a : A.LP (A.plGw k v)), (A.items₂ k (A.plGw k v) a).natDegree = A.lpDim a →
    Squarefree (A.items₂ k (A.plGw k v) a) → 16 * A.lpDim a ^ 2 < H.g k → Nc N A a
end

def FullBase (D : D7) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k), (labSig D Sig k v).natDegree = D.naut.lpDim (isoLoc D.nd D.naut Sig (D.naut.plGw k v))

def FullLabS (D : D7) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) : Prop :=
  FullBase D Sig ∧ ∀ (k : Fin 2) (v : D.nd.PlG k), Nc D.nd D.naut (isoLoc D.nd D.naut Sig (D.naut.plGw k v))

theorem fl0' {D : D7} {Sig : List (Formalism.BasicNotions.Part D.naut.CG)} (h : FullLabS D Sig) : FullBase D Sig := h.1
theorem fullLabS_of_fullLabS_trivial {D : D7} {Sig : List (Formalism.BasicNotions.Part D.naut.CG)} (h : FullLabS D Sig) : FullLabS D Sig := h

def ResidualTameEigenvalueCondition (D : D7) (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) : Prop :=
    ∀ k : Fin 2, D.nd.l i ≠ D.host.g k →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      (∀ v : D.nd.PlG k, ∃ ι : Formalism.CyclotomicNorms.Fbar (D.host.g k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i),
        (∀ x y : Formalism.CyclotomicNorms.Fbar (D.host.g k), x ≠ 0 → y ≠ 0 → (orderOf x).Coprime (D.nd.l i) →
          (orderOf y).Coprime (D.nd.l i) → ι x = ι y → x = y) ∧
        Matrix.charpoly ((redF D i ρ (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
            Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
          ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k (D.naut.plGw k v)
              (isoLoc D.nd D.naut Sig (D.naut.plGw k v)))).map
            fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x))).prod ∧
        ∃ φ : G D.host.E D.nd.Om,
          redF D i ρ (φ * D.ntypes.tg k v * φ⁻¹) = redF D i ρ (D.ntypes.tg k v) ^ D.host.g k) ∧
      (∀ w ∈ placesOver D.host.E (D.host.g k), TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) →
        ∃ (v : D.nd.PlG k) (j : Fin D.R.m) (ι : Formalism.CyclotomicNorms.Fbar (D.host.g k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i))
          (e₁ e₂ : ℤ), (e₁ = 1 ∨ e₁ = -1) ∧ (e₂ = 1 ∨ e₂ = -1) ∧
          (∀ x y : Formalism.CyclotomicNorms.Fbar (D.host.g k), x ≠ 0 → y ≠ 0 → (orderOf x).Coprime (D.nd.l i) →
            (orderOf y).Coprime (D.nd.l i) → ι x = ι y → x = y) ∧
          Matrix.charpoly ((redF D i ρ (D.nd.gam0 i w) : GL (Fin D.R.r) _) :
              Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
            ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k (D.naut.plGw k v)
                (isoLoc D.nd D.naut Sig (D.naut.plGw k v)))).map
              fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x) ^ e₁)).prod ∧
          D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) =
            ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i)
              (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
                ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)))) ^ e₂)

def AdmissibleResidualTameEigenvalues (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)), (∃ x, HasParamX D.nd D.naut i x Sig) → FullBase D Sig →
    (∀ k v, Squarefree (labSig D Sig k v)) → IsCuspIso D.nd D.naut Sig →
    ∀ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i), IsRepOfSig D.nd D.naut i Sig ρ → ResidualTameEigenvalueCondition D i Sig ρ

theorem g3p {D : D7} (h : LabelDegreeHypotheses D) : AdmissibleResidualTameEigenvalues D := fun i Sig hx hf _ => h i Sig hx hf
theorem g3p' {D : D7} (h : AdmissibleResidualTameEigenvalues D) : AdmissibleResidualTameEigenvalues D := h

end UpperTheory.GalS
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bridge
section
noncomputable section

namespace UpperTheory.GalS

open Formalism.MainNotions.SumRepresentations Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal Topology

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i)))

private theorem exists_isCompl_finrank_inertia_of_charpoly (A : NAut N) (hr : GoodR N i r) (hTY : At.MonodromyInertiaType N A)
    (w : PlE H) (hS : w ∈ N.S i) (hg : ∃ k, w ∈ placesOver H.E (H.g k)) (hL : LGCatN N r A w)
    (hmult : ∀ x, rootMultiplicity (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w)))
      (((redRep N i (r x) (N.gam0 i w) : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) _).charpoly) = R.t)
    (x : N.X i) :
    ∃ U U' : Submodule (Qbar (N.l i)) (Fin R.nV → Qbar (N.l i)), IsCompl U U' ∧
      Module.finrank (Qbar (N.l i)) U' = R.t ∧
      ∀ γ ∈ Ine (F := H.E) (N.plOm.1 w),
        (∀ v ∈ U, ((mapRep (iotaOQ N A i) (r x) γ : GL _ _) :
            Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))).mulVec v ∈ U) ∧
        ∀ v ∈ U', ((mapRep (iotaOQ N A i) (r x) γ : GL _ _) :
            Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))).mulVec v = iotaOQ N A i (chi1 N i γ) • v := by
  have hw : w ∉ placesOver H.E (N.l i) := N.SQ_l i w (Or.inl hS)
  have hcont : Continuous fun g => ((mapRep (iotaOQ N A i) (r x) g : GL _ _) :
      Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))) :=
    contQ_of_continuous N A i (r x) (hr x).1
  obtain ⟨P, -, hP0⟩ := hL x
  obtain ⟨s, hP⟩ : ∃ s : ℝ, RelU N A (A.wdOf i (mapRep (iotaOQ N A i) (r x)) w)
      (A.lpTw (A.locV i P w) s) := ⟨_, hP0⟩
  have hγ₀I : N.gam0 i w ∈ Ine (F := H.E) (N.plOm.1 w) := N.locNd_chebotarevPlace_mem i w
  have htame := (N.restN_tameGenerator_generates i w (Or.inl hS)).2
  have hcpQ : ∀ g, (((mapRep (iotaOQ N A i) (r x) g : GL _ _) :
      Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))).charpoly =
      (((r x g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i))).charpoly.map (iotaOQ N A i) :=
    fun g => Matrix.charpoly_map _ _
  have hle : rootMultiplicity (iotaOQ N A i (chi1 N i (N.gam0 i w)))
      (((mapRep (iotaOQ N A i) (r x) (N.gam0 i w) : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))).charpoly ≤ R.t := by
    rw [hcpQ, ← hmult x]
    refine (rootMult_le_of_maps (iotaOQ N A i) (iotaOQ_injective N A i)
      (IsLocalRing.residue (N.O i)) _ (Matrix.charpoly_monic _) _).trans (le_of_eq ?_)
    rw [← Matrix.charpoly_map]
    rfl
  have hine : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
      (((mapRep (iotaOQ N A i) (r x) σ : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))).charpoly.map (A.iotaQC i).toRingHom =
        A.inePol (A.locV i P w) σ := fun σ hσ =>
    ((A.wdOf_ine i _ w hw hcont σ hσ).trans (hP.ine σ hσ)).trans (A.inePol_tw _ s σ hσ)
  have hdim : A.lpDim (A.locV i P w) = R.nV := by
    rw [← A.lpDim_tw _ s, ← hP.dim, A.wdOf_dim]
  have hne : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locV i P w) σ ≠ 0 := by
    intro σ hσ
    rw [← hine σ hσ]
    exact ((Matrix.charpoly_monic _).map _).ne_zero
  have hleC : rootMultiplicity (iotaO N A i (chi1 N i (N.gam0 i w)))
      (A.inePol (A.locV i P w) (N.gam0 i w)) ≤ R.t := by
    rw [← hine _ hγ₀I]
    exact (eq_rootMultiplicity_map (A.iotaQC i).injective _).symm.trans_le hle
  obtain ⟨a, b, hab, -, -, -, hb⟩ := hTY.2.1 i P w hS hg htame hleC
  have hdivC : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
      (X - C (iotaO N A i (chi1 N i σ))) ^ R.t ∣ A.inePol (A.locV i P w) σ := by
    intro σ hσ
    rw [hab, A.inePol_sum, hb σ hσ]
    exact dvd_mul_left _ _
  have hge : R.t ≤ rootMultiplicity (iotaOQ N A i (chi1 N i (N.gam0 i w)))
      (((mapRep (iotaOQ N A i) (r x) (N.gam0 i w) : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))).charpoly := by
    have h1 := (le_rootMultiplicity_iff (hne _ hγ₀I)).mpr (hdivC _ hγ₀I)
    rw [← hine _ hγ₀I] at h1
    exact h1.trans_eq (eq_rootMultiplicity_map (A.iotaQC i).injective _).symm
  have hinj : Function.Injective (Polynomial.map (R := Qbar (N.l i)) (A.iotaQC i).toRingHom) :=
    Polynomial.map_injective _ (A.iotaQC i).injective
  have ht0 : R.t ≠ 0 := fun h => by
    have := R.t_odd
    rw [h] at this
    exact (Nat.not_odd_zero this)
  have hiO : Function.Injective (iotaO N A i) := fun a b h =>
    iotaOQ_injective N A i ((A.iotaQC i).injective h)
  obtain ⟨χ, hχ⟩ : ∃ χ : G H.E N.Om →* (Qbar (N.l i))ˣ,
      χ = (Units.map (iotaOQ N A i).toMonoidHom).comp (N.chi i 1) := ⟨_, rfl⟩
  have hχv : ∀ g, ((χ g : (Qbar (N.l i))ˣ) : Qbar (N.l i)) = iotaOQ N A i (chi1 N i g) := by
    intro g
    rw [hχ]
    rfl
  have hχcont : Continuous fun g => ((χ g : (Qbar (N.l i))ˣ) : Qbar (N.l i)) := by
    simp only [hχv]
    exact (continuous_iotaOQ N A i).comp (N.chi_cont i 1)
  have hfin := (A.wdOf_mono0 i _ w hw hcont).mp hP.mono
  have hfo : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), IsOfFinOrder (mapRep (iotaOQ N A i) (r x) σ) := by
    intro σ hσ
    refine finite_zpowers.mp (hfin.subset ?_)
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ⟨σ ^ k, Subgroup.zpow_mem _ hσ k, map_zpow _ σ k⟩
  have hwild : ∀ σ ∈ wildSet N (N.plOm.1 w), σ ∈ Ine (F := H.E) (N.plOm.1 w) ∧
      (((mapRep (iotaOQ N A i) (r x) σ : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))).charpoly = (X - 1) ^ R.nV ∧ χ σ = 1 := by
    intro σ hσ
    have hσI : σ ∈ Ine (F := H.E) (N.plOm.1 w) := GlobalTheory.TameEig.wild_mem_Ine (N.plOm.1 w) σ hσ
    have hX : A.inePol (A.locV i P w) σ = (X - 1) ^ R.nV := by
      rw [← A.inePol_tw _ s σ hσI, hP.nice.1 σ hσI hσ, A.lpDim_tw, hdim]
    refine ⟨hσI, ?_, ?_⟩
    · apply hinj
      rw [hine σ hσI, hX]
      simp
    · have h1 := hdivC σ hσI
      rw [hX, show (X - 1 : Polynomial ℂ) = X - C 1 by simp] at h1
      have h2 := (Polynomial.prime_X_sub_C (iotaO N A i (chi1 N i σ))).dvd_of_dvd_pow
        ((dvd_pow_self _ ht0).trans h1)
      have h3 := Polynomial.dvd_iff_isRoot.mp h2
      rw [Polynomial.root_X_sub_C] at h3
      have h4 : chi1 N i σ = 1 := hiO (by rw [← h3, map_one])
      ext
      rw [hχv, h4, map_one]
      rfl
  have hm : rootMultiplicity ((χ (N.gam0 i w) : (Qbar (N.l i))ˣ) : Qbar (N.l i))
      (((mapRep (iotaOQ N A i) (r x) (N.gam0 i w) : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))).charpoly = R.t := by
    rw [hχv]
    exact le_antisymm hle hge
  obtain ⟨U, U', hUU, hd, hact⟩ := split_tame (Ine (F := H.E) (N.plOm.1 w))
    (wildSet N (N.plOm.1 w)) (N.gam0 i w) hγ₀I htame (mapRep (iotaOQ N A i) (r x)) hcont χ hχcont
    hfo hwild hm
  refine ⟨U, U', hUU, hd, fun γ hγ => ⟨(hact γ hγ).1, fun v hv => ?_⟩⟩
  rw [(hact γ hγ).2 v hv, hχv]

theorem exists_inertia_charpoly_factor_of_tame_type (A : NAut N) (hC : Cheb N) (hr : GoodR N i r) (hT : At.TieGal N A) (hTY : At.MonodromyInertiaType N A)
    (w : PlE H) (hS : w ∈ N.S i) (hg : ∃ k, w ∈ placesOver H.E (H.g k))
    (hL : LGCatN N r A w)
    (rb : G H.E N.Om →* GL (Fin R.r) (IsLocalRing.ResidueField (N.O i))) (hrb : IsRhoBar N i rb)
    (hnr : ¬ (((rb (N.gam0 i w) : GL _ _) : Matrix (Fin R.r) (Fin R.r) _).charpoly).IsRoot
      (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w)))) :
    ∃ Pp : Polynomial (N.T i),
      IsUnit (Pp.eval (algebraMap (N.O i) (N.T i) (chi1 N i (N.gam0 i w)))) ∧
      ∀ x, ∀ γ ∈ Ine (F := H.E) (N.plOm.1 w),
        Polynomial.aeval ((r x (N.gam0 i w) : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i))
            (Pp.map ((Pi.evalRingHom (fun _ : N.X i => N.O i) x).comp (N.T i).val.toRingHom)) *
          (((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)) - chi1 N i γ • 1) = 0 := by
  have hw : w ∉ placesOver H.E (N.l i) := N.SQ_l i w (Or.inl hS)
  exact weil_deligne_clause_of_split N r (charpoly_clause_of_chebotarev N hC i r hr) w (iotaOQ N A i) (iotaOQ_injective N A i)
    (exists_isCompl_finrank_inertia_of_charpoly N r A hr hTY w hS hg hL (mult_of_rhobar N r hC hr rb hrb w hw hnr))
    (mult_of_rhobar N r hC hr rb hrb w hw hnr)

theorem SplitI_of_TY (A : NAut N) (hr : GoodR N i r) (w : PlE H) (hw : w ∉ placesOver H.E (N.l i))
    (hL : LGCatN N r A w)
    (hty : ∀ P : A.AV i, A.mono0 (A.locV i P w) ∧ ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
      A.inePol (A.locV i P w) σ = (X - 1) ^ R.r * (X - C (iotaO N A i (chi1 N i σ))) ^ R.t)
    (x : N.X i) : SplitI N r w x := by
  have hcont : Continuous fun g => ((mapRep (iotaOQ N A i) (r x) g : GL _ _) :
      Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))) :=
    contQ_of_continuous N A i (r x) (hr x).1
  obtain ⟨P, -, hP0⟩ := hL x
  obtain ⟨s, hP⟩ : ∃ s : ℝ, RelU N A (A.wdOf i (mapRep (iotaOQ N A i) (r x)) w)
      (A.lpTw (A.locV i P w) s) := ⟨_, hP0⟩
  have hine : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
      (((mapRep (iotaOQ N A i) (r x) σ : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))).charpoly.map (A.iotaQC i).toRingHom =
        A.inePol (A.locV i P w) σ := fun σ hσ =>
    ((A.wdOf_ine i _ w hw hcont σ hσ).trans (hP.ine σ hσ)).trans (A.inePol_tw _ s σ hσ)
  have hfin := (A.wdOf_mono0 i _ w hw hcont).mp hP.mono
  have ht0 : R.t ≠ 0 := fun h => by
    have := R.t_odd
    rw [h] at this
    exact (Nat.not_odd_zero this)
  haveI : CharZero (Kf N i) := ((A.iotaQC i).toRingHom.comp (A.iotaQ i)).charZero
  let ρ : Ine (F := H.E) (N.plOm.1 w) →* GL (Fin (R.r + R.t)) (Kf N i) :=
    (mapRep (algebraMap (N.O i) (Kf N i)) (r x)).comp (Ine (F := H.E) (N.plOm.1 w)).subtype
  let χ : Ine (F := H.E) (N.plOm.1 w) →* (Kf N i)ˣ :=
    ((Units.map (algebraMap (N.O i) (Kf N i)).toMonoidHom).comp (N.chi i 1)).comp
      (Ine (F := H.E) (N.plOm.1 w)).subtype
  have hrange : (Set.range ρ).Finite := by
    refine Set.Finite.of_finite_image (f := Units.map
      (RingHom.toMonoidHom (RingHom.mapMatrix (m := Fin (R.r + R.t)) (A.iotaQ i)))) ?_ ?_
    · refine hfin.subset ?_
      rintro _ ⟨_, ⟨γ, rfl⟩, rfl⟩
      exact ⟨γ.1, γ.2, Units.ext rfl⟩
    · intro u _ v _ h
      apply Units.ext
      have h' := congrArg (fun z : GL (Fin (R.r + R.t)) (Qbar (N.l i)) =>
        (z : Matrix (Fin (R.r + R.t)) (Fin (R.r + R.t)) (Qbar (N.l i)))) h
      exact Matrix.map_injective (A.iotaQ i).injective h'
  have hcp : ∀ γ, ((ρ γ : GL _ _) : Matrix (Fin (R.r + R.t)) (Fin (R.r + R.t)) (Kf N i)).charpoly =
      (X - 1) ^ R.r * (X - C ((χ γ : (Kf N i)ˣ) : Kf N i)) ^ R.t := by
    intro γ
    apply Polynomial.map_injective ((A.iotaQC i).toRingHom.comp (A.iotaQ i))
      ((A.iotaQC i).toRingHom.comp (A.iotaQ i)).injective
    have hmat : ((ρ γ : GL _ _) : Matrix (Fin (R.r + R.t)) (Fin (R.r + R.t)) (Kf N i)).map (A.iotaQ i) =
        ((mapRep (iotaOQ N A i) (r x) γ.1 : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))) :=
      rfl
    rw [← Polynomial.map_map, ← Matrix.charpoly_map, hmat]
    refine (hine γ.1 γ.2).trans ?_
    rw [(hty P).2 γ.1 γ.2]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_one, Polynomial.map_C]
    rfl
  obtain ⟨Pm, hPm⟩ := split_of_charpoly ht0 ρ χ hrange hcp
  exact ⟨Pm, fun γ hγ => hPm ⟨γ, hγ⟩⟩

end UpperTheory.GalS
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.DistinctAbsIrredConstituents
section
noncomputable section

namespace UpperTheory.GalS

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain Formalism.MainNotions.SumRepresentations Formalism.MainNotions.SumRepresentations.At

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

def DistinctAbsIrredConstituents (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∃ (K' : Type) (_ : Field K') (_ : Algebra (Kf N i) K') (_ : FiniteDimensional (Kf N i) K'),
    ∀ x, (∀ W, IsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W →
        AbsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W) ∧
      ∀ W₁ W₂, IsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W₁ →
        IsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W₂ →
        W₁ ⊓ W₂ = ⊥ →
        ¬ IsoSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W₁ W₂

def G3a (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop :=
  ((N.l i ≠ H.g 0 ∧ N.l i ≠ H.g 1) ∨ GlobalTheory.CoefDuty.Live N i) → DistinctAbsIrredConstituents N i r

def ResidualCharpolyIndependent (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∀ (x y : N.X i) (g : G H.E N.Om),
    ((redRep N i (r x) g : GL (Fin R.nV) (IsLocalRing.ResidueField (N.O i))) :
        Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))).charpoly =
      ((redRep N i (r y) g : GL (Fin R.nV) (IsLocalRing.ResidueField (N.O i))) :
        Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))).charpoly

def G3 (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop := G3a N i r ∧ ResidualCharpolyIndependent N i r

variable {N}
theorem g3 {i : N.Loc} {r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))} (h : At.G3 N i r) : G3 N i r := ⟨fun _ => h.1, h.2⟩
theorem g3' {i : N.Loc} {r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))} (h : G3 N i r) : G3 N i r := h
end

def DeRhamJumpsDistinctCondition (D : D7) : Prop :=
  (∀ i r, GoodR D.nd i r → (D.nd.l i = D.host.g 0 ∨ D.nd.l i = D.host.g 1) →
    ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ x,
      D.naut.IsdRW i (AdmissibleParameterJ.rQ D i r x) w ∧
      ∀ τ₀, InducesW D.nd i τ₀ w → D.naut.jumpsW i (AdmissibleParameterJ.rQ D i r x) τ₀ = D.naut.locAutHodgeTateWeightsLevelZero i τ₀) ∧
  ∀ i r, GoodR D.nd i r → DistinctAbsIrredConstituents D.nd i r

end UpperTheory.GalS
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.EtaPiece
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCGal

open Formalism.MainNotions.SumRepresentations.At GlobalTheory.TwistLG

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem galois_relation_away_from_l (hLP : TieLP N A) (hAut : TieAut N A) (hGal : TieGal N A) (hG : UpperTheory.GalS.AutomorphicGaloisAdmissible N A)
    {a : ℕ} (ha : 1 ≤ a) (π : A.CG a) (hc : A.csd π) (m : ℤ)
    (hinf : ∀ τ, (A.infG π τ).Nodup ∧
      ∀ z ∈ A.infG π τ, ∃ n : ℤ, z + (((m : ℝ) / 2 : ℝ) : ℂ) = (n : ℂ) + ((a : ℂ) - 1) / 2) :
    ∃ r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i)), ContQ N i r ∧ IsSSRep r ∧ ∀ w, w ∉ placesOver H.E (N.l i) →
      UpperTheory.GalS.RelW N A (A.wdOf i r w) (A.lpTw (A.locG π w) ((m : ℝ) / 2 + (1 - (a : ℝ)) / 2)) := by
  obtain ⟨-, -, -, htw⟩ := hGal.2.2.2 i
  rcases Int.even_or_odd' m with ⟨k, hk | hk⟩ <;> subst hk
  ·
    have hralg : A.ralg π := (A.ralg_def π).2 fun τ => ⟨(hinf τ).1, fun z hz => by
      obtain ⟨n, hn⟩ := (hinf τ).2 z hz
      exact ⟨n - k, by push_cast at hn ⊢; linear_combination hn⟩⟩
    obtain ⟨ρ1, c1, ss1, away1, -⟩ := (hG i).1 a ha π hc hralg
    obtain ⟨χA, cA, awayA, -⟩ := (hG i).2.2 A.etaT (1 / 2) fun τ z hz => by
      obtain ⟨n, hn⟩ := (eta_alg N A hAut 0 τ).1 z hz
      exact ⟨n, by push_cast at hn ⊢; linear_combination hn⟩
    obtain ⟨χB, cB, awayB, -⟩ := (hG i).2.2 A.etaTinv ((k : ℝ) - 1 / 2) fun τ z hz => by
      obtain ⟨n, hn⟩ := (eta_alg N A hAut (k - 1) τ).2 z hz
      exact ⟨n, by push_cast at hn ⊢; linear_combination hn⟩
    let ρ2 := twGL ρ1 (Matrix.GeneralLinearGroup.det.comp χA)
    have c2 : ContQ N i ρ2 := cont_twGL ρ1 χA c1 cA
    refine ⟨twGL ρ2 (Matrix.GeneralLinearGroup.det.comp χB), cont_twGL ρ2 χB c2 cB,
      isSSRep_twGL _ _ (isSSRep_twGL _ _ ss1), fun w hw => ?_⟩
    rw [(htw a ρ2 χB c2 cB).2.1 w (Or.inl hw) (Or.inl hw), (htw a ρ1 χA c1 cA).2.1 w (Or.inl hw) (Or.inl hw),
      awayA w hw, awayB w hw]
    have k1 := ((away1 w hw).char hLP (A.lpTw (A.locG A.etaT w) (1 / 2)) (by rw [A.lpDim_tw, A.locG_dim])
      ((A.unr_tw _ _).2 (A.etaT_unr w))).char hLP (A.lpTw (A.locG A.etaTinv w) ((k : ℝ) - 1 / 2))
      (by rw [A.lpDim_tw, A.locG_dim]) ((A.unr_tw _ _).2 (A.etaTinv_def w).1)
    rw [param_int N A hLP] at k1
    convert k1 using 2
    push_cast
    ring
  ·
    have hcsd : A.csd (A.tw π A.etaT) := A.csd_tw π A.etaT hAut.1.1 hc
    have hralg : A.ralg (A.tw π A.etaT) := (A.ralg_def _).2 fun τ => by
      obtain ⟨e, he⟩ := Multiset.card_eq_one.mp (A.infG_card A.etaT τ)
      rw [A.infG_tw π A.etaT τ e he]
      refine ⟨(hinf τ).1.map (add_left_injective e), fun y hy => ?_⟩
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
      obtain ⟨n, hn⟩ := (hinf τ).2 z hz
      obtain ⟨j, hj⟩ := (eta_alg N A hAut 0 τ).1 e (by rw [he]; exact Multiset.mem_singleton_self e)
      exact ⟨n + j - k - 1, by push_cast at hn hj ⊢; linear_combination hn + hj⟩
    obtain ⟨ρ1, c1, ss1, away1, -⟩ := (hG i).1 a ha _ hcsd hralg
    obtain ⟨χ1, cχ, awayχ, -⟩ := (hG i).2.2 A.etaTinv ((k : ℝ) + 1 / 2) (eta_alg N A hAut k · |>.2)
    refine ⟨twGL ρ1 (Matrix.GeneralLinearGroup.det.comp χ1), cont_twGL ρ1 χ1 c1 cχ, isSSRep_twGL _ _ ss1,
      fun w hw => ?_⟩
    rw [(htw a ρ1 χ1 c1 cχ).2.1 w (Or.inl hw) (Or.inl hw), awayχ w hw]
    have k1 := (away1 w hw).char hLP (A.lpTw (A.locG A.etaTinv w) ((k : ℝ) + 1 / 2))
      (by rw [A.lpDim_tw, A.locG_dim]) ((A.unr_tw _ _).2 (A.etaTinv_def w).1)
    rw [param_twist N A hLP] at k1
    convert k1 using 2
    push_cast
    ring

end GlobalTheory.BCGal
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TwListSs
section
noncomputable section

namespace GlobalTheory.EigenPoint

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

section Alg

variable {Γ : Type} [Group Γ] {K : Type} [Field K]

end Alg

variable (D : D7) (i : D.nd.Loc)

theorem isSSRep_of_mem_twList (Pa : List (Part D.naut.CG))
    (R : ∀ k : Fin Pa.length, G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i)))
    (hR : ∀ k, UpperTheory.GalS.IsStringRepN D i (Pa.get k) (R k)) : ∀ p ∈ twList D i Pa R, IsSSRep p.2 := by
  intro p hp
  obtain ⟨k, a, -, rfl⟩ := mem_twList D i hp
  exact ss_twGL _ _ (hR k).2.1

end GlobalTheory.EigenPoint
end
end

