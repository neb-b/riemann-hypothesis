module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Mathlib
public import Formalism.UnipotentAdelicQuotients.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1660
public import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTupleThetaKernelTameCharacter
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnBaseKer


open Classical in
theorem kerDat_of_isBaseKernel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → ∀ ω φ, IsBaseKernel R i v (ownAt D v) ω φ → ∃ χ ξR, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i v hv hmu ω φ hK
  obtain ⟨χ, ξR, hchr, hres, hweil, hvec⟩ := hK
  have hD := GlobalTheory.BigOn.isDelta_delAt_ownAt R.C v
  obtain ⟨ψ, Qw, hψ, hxi⟩ := hmu v hv
  have hL := hC.lev
  have hmem : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ), ((n : 𝓞 D.host.E) ∈ P.asIdeal ↔ Formalism.EigenvalueLevelCeiling.plc P ∣ n) :=
    fun P n => by
      unfold Formalism.EigenvalueLevelCeiling.plc
      rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk P.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
  have hstar : ∀ (n : ℕ) (c : 𝓞 D.host.E), (c : D.host.E) = star ((n : 𝓞 D.host.E) : D.host.E) → c = n := by
    intro n c h
    apply RingOfIntegers.coe_injective
    refine h.trans ?_
    simp
  refine ⟨χ, ξR, ⟨hchr, hD.fin, hD.triv, hD.tame, ?_, ?_, ?_, hres, hweil, hvec⟩⟩
  · intro PP hP
    have hP' := (Finset.mem_filter.1 hP).1
    exact ⟨(hL.Q_pl _ PP hP').1, fun PP' hP'' => (hL.Q_pl _ PP hP').2 PP' (Finset.mem_filter.1 hP'').1⟩
  · intro PP hP
    exact (hL.Q_off _ PP (Finset.mem_filter.1 hP).1).1
  · intro PP
    constructor
    · intro hnu
      have hover : ((ownAt D v : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
        by_contra h
        exact hnu (hD.unr PP h)
      have hram : ¬ (R.xiH (R.mu v)).UnrAt PP := by
        rw [hxi]
        intro hu
        obtain ⟨a, ha⟩ := hψ.ord
        have h15 : 15 ∣ Formalism.EigenvalueLevelCeiling.plc v ^ a := by
          refine (hD.ine PP hover _).1 fun x hx => ?_
          have h1 := hu x hx
          have loc_mul (a b : Formalism.L2.Host.HChar D.host.E) :
              (a * b).loc PP x = a.loc PP x * b.loc PP x := rfl
          rw [loc_mul] at h1
          have h2 : ψ.loc PP x ^ (Formalism.EigenvalueLevelCeiling.plc v ^ a) = 1 := by
            have h3 := congrArg (fun χ' : Formalism.L2.Host.HChar D.host.E => χ'.loc PP x) ha
            exact h3
          rw [eq_inv_of_mul_eq_one_left h1, inv_pow, h2, inv_one]
        have hl := Formalism.EigenvalueLevelCeiling.plc_prime v
        have h3 : 3 = Formalism.EigenvalueLevelCeiling.plc v := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hl).1
          (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
        have h5 : 5 = Formalism.EigenvalueLevelCeiling.plc v := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hl).1
          (Nat.prime_five.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
        omega
      rcases (hL.Q_ram _ PP).1 hram with h | ⟨PP', h, hc⟩
      · exact Or.inl (Finset.mem_filter.2 ⟨h, hover⟩)
      · refine Or.inr ⟨PP', Finset.mem_filter.2 ⟨h, ?_⟩, hc⟩
        obtain ⟨c', hc', he⟩ := hc _ ((hmem PP' _).2 dvd_rfl)
        rw [hstar _ _ he, hmem] at hc'
        have heq := (Nat.prime_dvd_prime_iff_eq (Formalism.EigenvalueLevelCeiling.plc_prime PP) (Formalism.EigenvalueLevelCeiling.plc_prime PP')).1 hc'
        rw [hmem] at hover ⊢
        exact heq ▸ hover
    · intro h hu
      have hover : ((ownAt D v : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
        rcases h with h | ⟨PP', h, hc⟩
        · exact (Finset.mem_filter.1 h).2
        · obtain ⟨c', hc', he⟩ := hc _ (Finset.mem_filter.1 h).2
          rwa [hstar _ _ he] at hc'
      have h1 := (hD.ine PP hover 1).1 fun x hx => by rw [pow_one]; exact hu x hx
      norm_num at h1

end GlobalTheory.OnBaseKer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BorelFiniteClassNumberCentraliserTorus
section
noncomputable section

open NumberField GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.TorCls.Borel

variable {N : ℕ} {S : Set (MvPolynomial (Fin N × Fin N) ℚ)} (hS : HeckeCharacterZeroLocus.IsGroupLocus S)

theorem aeval_map_entries {R R' : Type} [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R']
    (f : R →ₐ[ℚ] R') (M : Matrix (Fin N) (Fin N) R) (P : MvPolynomial (Fin N × Fin N) ℚ) :
    MvPolynomial.aeval (fun ij : Fin N × Fin N => f (M ij.1 ij.2)) P =
      f (MvPolynomial.aeval (fun ij : Fin N × Fin N => M ij.1 ij.2) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem mem_locus_map {R R' : Type} [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R')
    (g : HeckeCharacterZeroLocus.locusSubgroup S hS R) :
    Units.map (f.toRingHom.mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R').toMonoidHom
      (g : GL (Fin N) R) ∈ HeckeCharacterZeroLocus.locusSubgroup S hS R' := by
  intro P hP
  have h := g.2 P hP
  show MvPolynomial.aeval (fun ij : Fin N × Fin N => f (((g : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) ij.1 ij.2)) P = 0
  rw [aeval_map_entries, h, map_zero]

def locMap {R R' : Type} [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R') :
    HeckeCharacterZeroLocus.locusSubgroup S hS R →* HeckeCharacterZeroLocus.locusSubgroup S hS R' :=
  ((Units.map (f.toRingHom.mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R').toMonoidHom).comp
    (HeckeCharacterZeroLocus.locusSubgroup S hS R).subtype).codRestrict _ (mem_locus_map hS f)

theorem locMap_comp {R R' R'' : Type} [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R']
    [CommRing R''] [Algebra ℚ R''] (f : R' →ₐ[ℚ] R'') (f' : R →ₐ[ℚ] R') (g : HeckeCharacterZeroLocus.locusSubgroup S hS R) :
    locMap hS f (locMap hS f' g) = locMap hS (f.comp f') g := rfl

theorem continuous_locMap {R R' : Type} [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [CommRing R']
    [Algebra ℚ R'] [TopologicalSpace R'] (f : R →ₐ[ℚ] R') (hf : Continuous f) :
    Continuous (locMap hS f) := by
  refine Continuous.subtype_mk ?_ _
  refine (Continuous.units_map _ ?_).comp continuous_subtype_val
  exact Continuous.matrix_map continuous_id hf

theorem lid_starT {D : Type} [Ring D] [Algebra ℚ D] (σ : D →+* Dᵐᵒᵖ) (x : ℚ ⊗[ℚ] D) :
    Algebra.TensorProduct.lid ℚ D (starT σ ℚ x).unop = (σ (Algebra.TensorProduct.lid ℚ D x)).unop := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul q d =>
    rw [starT_tmul, Algebra.TensorProduct.lid_tmul, Algebra.TensorProduct.lid_tmul, map_rat_smul,
      MulOpposite.unop_smul]
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]

theorem map_ofId_eq {D B : Type} [Ring D] [Algebra ℚ D] [CommRing B] [Algebra ℚ B] (x : ℚ ⊗[ℚ] D) :
    Algebra.TensorProduct.map (Algebra.ofId ℚ B) (AlgHom.id ℚ D) x =
      (Algebra.TensorProduct.includeRight : D →ₐ[ℚ] B ⊗[ℚ] D) (Algebra.TensorProduct.lid ℚ D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul q d =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul, Algebra.TensorProduct.includeRight_apply,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', AlgHom.id_apply, Algebra.ofId_apply,
      Algebra.algebraMap_eq_smul_one]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tc_rat {D : Type} [Ring D] [Algebra ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (z : (ℚ ⊗[ℚ] D)ˣ × ℚˣ)
    (h : GlobalTheory.TorCls.TC D σ β y ℚ z) :
    Algebra.TensorProduct.lid ℚ D (z.1 : ℚ ⊗[ℚ] D) * β * (σ (Algebra.TensorProduct.lid ℚ D (z.1 : ℚ ⊗[ℚ] D))).unop =
        algebraMap ℚ D (z.2 : ℚ) * β ∧
      Commute (Algebra.TensorProduct.lid ℚ D (z.1 : ℚ ⊗[ℚ] D)) y := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · have := congrArg (Algebra.TensorProduct.lid ℚ D) h1
    simp only [map_mul, lid_starT] at this
    simpa [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one] using this
  · have := h2.map (Algebra.TensorProduct.lid ℚ D)
    simpa using this

end GlobalTheory.TorCls.Borel

namespace GlobalTheory.TorCls.Borel

open IsDedekindDomain

theorem classes_finite : (∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D),
  ∃ (N : ℕ) (S : Set (MvPolynomial (Fin N × Fin N) ℚ)) (hS : HeckeCharacterZeroLocus.IsGroupLocus S)
    (φ : ∀ (R : Type) [CommRing R] [Algebra ℚ R], HeckeCharacterZeroLocus.locusSubgroup S hS R →* (R ⊗[ℚ] D)ˣ × Rˣ),
    (∀ (R : Type) [CommRing R] [Algebra ℚ R], Function.Injective (φ R) ∧
      ∀ z : (R ⊗[ℚ] D)ˣ × Rˣ, GlobalTheory.TorCls.TC D σ β y R z ↔ z ∈ Set.range (φ R)) ∧
    (∀ (R R' : Type) [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R')
      (g : HeckeCharacterZeroLocus.locusSubgroup S hS R) (g' : HeckeCharacterZeroLocus.locusSubgroup S hS R'),
      (g' : GL (Fin N) R') = Units.map (f.toRingHom.mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R').toMonoidHom (g : GL (Fin N) R) →
      φ R' g' = (Units.map (Algebra.TensorProduct.map f (AlgHom.id ℚ D)).toRingHom.toMonoidHom (φ R g).1,
        Units.map f.toRingHom.toMonoidHom (φ R g).2)) ∧
    (∀ (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R],
      letI : TopologicalSpace (R ⊗[ℚ] D) := moduleTopology R (R ⊗[ℚ] D)
      Continuous (φ R))) → HeckeCharacterZeroLocus.ClassNumberFinite → ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (p : ℕ) [Fact p.Prime],
    letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D)
    letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D)
    ∀ U : Subgroup (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)),
      (∃ O : Set (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧
        ∀ z ∈ O, GlobalTheory.TorCls.TC D σ β y (AfP p) z.1 → GlobalTheory.TorCls.TC D σ β y ℚ_[p] z.2 → z ∈ U) →
      ∃ S : Finset (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)),
        ∀ z, GlobalTheory.TorCls.TC D σ β y (AfP p) z.1 → GlobalTheory.TorCls.TC D σ β y ℚ_[p] z.2 →
          ∃ γ : Dˣ × ℚˣ, (γ.1 : D) * β * (σ γ.1).unop = algebraMap ℚ D γ.2 * β ∧ Commute (γ.1 : D) y ∧
            ∃ s ∈ S, ∃ u ∈ U, z = GlobalTheory.TorCls.dg D p γ * s * u := by
  intro hbr hB D _ _ _ σ β y p _
  obtain ⟨N, S, hS, φ, hiso, hnat, hcont⟩ := hbr D σ β y
  letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D)
  letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D)
  intro U hUO
  obtain ⟨O, hO, h1O, hOU⟩ := hUO
  have hsplit : ∃ (π₁ : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] AfP p)
      (π₂ : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] ℚ_[p]),
      Continuous π₁ ∧ Continuous π₂ ∧ Function.Bijective (fun a => (π₁ a, π₂ a)) := by
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_continuous_finiteAdele_equiv_rat_int
    obtain ⟨π, hπc, hπb⟩ := GlobalTheory.T.ratFiniteAdeles_split_awayFromPrime_padic p
    let r : FiniteAdeleRing ℤ ℚ →ₐ[ℚ] AfP p := { AfP.restr p with commutes' := fun _ => rfl }
    exact ⟨r.comp e.toAlgHom, π.comp e.toAlgHom,
      (GlobalTheory.T.continuous_afP_restr p).comp he, hπc.comp he, hπb.comp e.bijective⟩
  obtain ⟨π₁, π₂, hc₁, hc₂, hbij⟩ := hsplit
  let Φ : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 ℚ) ℚ) →*
      ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ) :=
    ((φ (AfP p)).comp (locMap hS π₁)).prod ((φ ℚ_[p]).comp (locMap hS π₂))
  have hφ₁ : Continuous (φ (AfP p)) := hcont (AfP p)
  have hφ₂ : Continuous (φ ℚ_[p]) := hcont ℚ_[p]
  have hΦc : Continuous Φ :=
    (hφ₁.comp (continuous_locMap hS π₁ hc₁)).prodMk (hφ₂.comp (continuous_locMap hS π₂ hc₂))
  have hTC : ∀ g, GlobalTheory.TorCls.TC D σ β y (AfP p) (Φ g).1 ∧ GlobalTheory.TorCls.TC D σ β y ℚ_[p] (Φ g).2 := fun g =>
    ⟨((hiso (AfP p)).2 _).2 ⟨_, rfl⟩, ((hiso ℚ_[p]).2 _).2 ⟨_, rfl⟩⟩

  have hsurj : ∀ z : ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ),
      GlobalTheory.TorCls.TC D σ β y (AfP p) z.1 → GlobalTheory.TorCls.TC D σ β y ℚ_[p] z.2 → ∃ g, Φ g = z := by
    intro z h1 h2
    obtain ⟨g₁, hg₁⟩ := ((hiso (AfP p)).2 z.1).1 h1
    obtain ⟨g₂, hg₂⟩ := ((hiso ℚ_[p]).2 z.2).1 h2
    let s := Function.surjInv hbij.2
    have hs : ∀ x, (π₁ (s x), π₂ (s x)) = x := Function.surjInv_eq hbij.2
    have hs₁ : ∀ a b, π₁ (s (a, b)) = a := fun a b => congrArg Prod.fst (hs (a, b))
    have hs₂ : ∀ a b, π₂ (s (a, b)) = b := fun a b => congrArg Prod.snd (hs (a, b))
    have hinj : ∀ a a' : FiniteAdeleRing (𝓞 ℚ) ℚ, π₁ a = π₁ a' → π₂ a = π₂ a' → a = a' :=
      fun a a' h h' => hbij.1 (Prod.ext h h')
    have hinjM : ∀ X Y : Matrix (Fin N) (Fin N) (FiniteAdeleRing (𝓞 ℚ) ℚ),
        π₁.toRingHom.mapMatrix X = π₁.toRingHom.mapMatrix Y →
        π₂.toRingHom.mapMatrix X = π₂.toRingHom.mapMatrix Y → X = Y := by
      intro X Y h h'
      refine Matrix.ext fun i j => ?_
      exact hinj _ _ (congrFun (congrFun h i) j) (congrFun (congrFun h' i) j)
    let G₁ : GL (Fin N) (AfP p) := g₁
    let G₂ : GL (Fin N) ℚ_[p] := g₂
    let M : Matrix (Fin N) (Fin N) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
      Matrix.of fun i j => s ((G₁ : Matrix (Fin N) (Fin N) (AfP p)) i j, (G₂ : Matrix (Fin N) (Fin N) ℚ_[p]) i j)
    let M' : Matrix (Fin N) (Fin N) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
      Matrix.of fun i j => s (((G₁⁻¹ : GL (Fin N) (AfP p)) : Matrix (Fin N) (Fin N) (AfP p)) i j,
        ((G₂⁻¹ : GL (Fin N) ℚ_[p]) : Matrix (Fin N) (Fin N) ℚ_[p]) i j)
    have hM₁ : π₁.toRingHom.mapMatrix M = (G₁ : Matrix (Fin N) (Fin N) (AfP p)) := by
      ext i j; exact hs₁ _ _
    have hM₂ : π₂.toRingHom.mapMatrix M = (G₂ : Matrix (Fin N) (Fin N) ℚ_[p]) := by
      ext i j; exact hs₂ _ _
    have hM'₁ : π₁.toRingHom.mapMatrix M' = ((G₁⁻¹ : GL (Fin N) (AfP p)) : Matrix (Fin N) (Fin N) (AfP p)) := by
      ext i j; exact hs₁ _ _
    have hM'₂ : π₂.toRingHom.mapMatrix M' = ((G₂⁻¹ : GL (Fin N) ℚ_[p]) : Matrix (Fin N) (Fin N) ℚ_[p]) := by
      ext i j; exact hs₂ _ _
    have hMM' : M * M' = 1 := hinjM _ _ (by rw [map_mul, map_one, hM₁, hM'₁]; simp)
      (by rw [map_mul, map_one, hM₂, hM'₂]; simp)
    have hM'M : M' * M = 1 := hinjM _ _ (by rw [map_mul, map_one, hM₁, hM'₁]; simp)
      (by rw [map_mul, map_one, hM₂, hM'₂]; simp)
    let G : GL (Fin N) (FiniteAdeleRing (𝓞 ℚ) ℚ) := ⟨M, M', hMM', hM'M⟩
    have hG : G ∈ HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 ℚ) ℚ) := by
      intro P hP
      apply hinj
      · rw [map_zero, ← aeval_map_entries]
        have e : (fun ij : Fin N × Fin N => π₁ ((G : Matrix (Fin N) (Fin N) (FiniteAdeleRing (𝓞 ℚ) ℚ)) ij.1 ij.2)) =
            fun ij => (G₁ : Matrix (Fin N) (Fin N) (AfP p)) ij.1 ij.2 := by
          funext ij; exact hs₁ _ _
        rw [e]; exact g₁.2 P hP
      · rw [map_zero, ← aeval_map_entries]
        have e : (fun ij : Fin N × Fin N => π₂ ((G : Matrix (Fin N) (Fin N) (FiniteAdeleRing (𝓞 ℚ) ℚ)) ij.1 ij.2)) =
            fun ij => (G₂ : Matrix (Fin N) (Fin N) ℚ_[p]) ij.1 ij.2 := by
          funext ij; exact hs₂ _ _
        rw [e]; exact g₂.2 P hP
    refine ⟨⟨G, hG⟩, Prod.ext ?_ ?_⟩
    · show φ (AfP p) (locMap hS π₁ ⟨G, hG⟩) = z.1
      rw [← hg₁]; congr 1; apply Subtype.ext; apply Units.ext; exact hM₁
    · show φ ℚ_[p] (locMap hS π₂ ⟨G, hG⟩) = z.2
      rw [← hg₂]; congr 1; apply Subtype.ext; apply Units.ext; exact hM₂

  let U' : Subgroup (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 ℚ) ℚ)) := U.comap Φ
  have hU'o : IsOpen (U' : Set (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 ℚ) ℚ))) := by
    apply Subgroup.isOpen_of_mem_nhds U' (g := 1)
    have h1 : (1 : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Φ ⁻¹' O := by
      show Φ 1 ∈ O; rw [map_one]; exact h1O
    refine Filter.mem_of_superset ((hO.preimage hΦc).mem_nhds h1) ?_
    intro g hg
    exact hOU _ hg (hTC g).1 (hTC g).2
  have hU'c : IsClosed (U' : Set (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 ℚ) ℚ))) :=
    U'.isClosed_of_isOpen hU'o
  obtain ⟨K, hKo, hKc⟩ := GlobalTheory.LocusOpenCompact.exists_isOpen_isCompact ℚ N S hS
  obtain ⟨T₀, hT₀⟩ := hB ℚ N S hS (U' ⊓ K) (by rw [Subgroup.coe_inf]; exact hU'o.inter hKo)
    (by
      rw [Subgroup.coe_inf]
      exact hKc.inter_left hU'c)

  classical
  refine ⟨T₀.image Φ, ?_⟩
  intro z h1 h2
  obtain ⟨g, rfl⟩ := hsurj z h1 h2
  obtain ⟨γ, hγ, s, hs, u, hu, hx⟩ := hT₀ g
  let γL : HeckeCharacterZeroLocus.locusSubgroup S hS ℚ := ⟨γ, hγ⟩
  have hg : g = locMap hS (Algebra.ofId ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) γL * s * u := Subtype.ext hx
  let w := φ ℚ γL
  have hw : GlobalTheory.TorCls.TC D σ β y ℚ w := ((hiso ℚ).2 w).2 ⟨γL, rfl⟩
  obtain ⟨hw1, hw2⟩ := tc_rat σ β y w hw
  let γ' : Dˣ × ℚˣ :=
    (Units.map (Algebra.TensorProduct.lid ℚ D).toAlgHom.toRingHom.toMonoidHom w.1, w.2)
  have hcomp₁ : π₁.comp (Algebra.ofId ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) = Algebra.ofId ℚ (AfP p) :=
    AlgHom.ext fun q => by simp
  have hcomp₂ : π₂.comp (Algebra.ofId ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) = Algebra.ofId ℚ ℚ_[p] :=
    AlgHom.ext fun q => by simp
  have hΦγ : Φ (locMap hS (Algebra.ofId ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) γL) = GlobalTheory.TorCls.dg D p γ' := by
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
    · show (φ (AfP p) (locMap hS π₁ (locMap hS _ γL))).1 = _
      rw [locMap_comp, hcomp₁, hnat ℚ (AfP p) (Algebra.ofId ℚ (AfP p)) γL _ rfl]
      apply Units.ext
      exact map_ofId_eq _
    · show (φ (AfP p) (locMap hS π₁ (locMap hS _ γL))).2 = _
      rw [locMap_comp, hcomp₁, hnat ℚ (AfP p) (Algebra.ofId ℚ (AfP p)) γL _ rfl]
      rfl
    · show (φ ℚ_[p] (locMap hS π₂ (locMap hS _ γL))).1 = _
      rw [locMap_comp, hcomp₂, hnat ℚ ℚ_[p] (Algebra.ofId ℚ ℚ_[p]) γL _ rfl]
      apply Units.ext
      exact map_ofId_eq _
    · show (φ ℚ_[p] (locMap hS π₂ (locMap hS _ γL))).2 = _
      rw [locMap_comp, hcomp₂, hnat ℚ ℚ_[p] (Algebra.ofId ℚ ℚ_[p]) γL _ rfl]
      rfl
  refine ⟨γ', hw1, hw2, Φ s, Finset.mem_image_of_mem _ hs, Φ u, (Subgroup.mem_inf.1 hu).1, ?_⟩
  rw [hg, map_mul, map_mul, hΦγ]

end GlobalTheory.TorCls.Borel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomRankSumLeTwoMulTotalRank
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop GlobalTheory.NormSum
open Formalism.L2.Host (HChar)

noncomputable section

namespace GlobalTheory.SqTop.BotSmallProof

theorem eq_of_dvd_absNorm {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {ℓ p : ℕ}
    (hℓ : ℓ.Prime) (hp : p.Prime) (hv : ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal) (h : p ∣ Ideal.absNorm v.asIdeal) : p = ℓ := by
  have hmax : (Ideal.span {((ℓ : ℕ) : ℤ)} : Ideal ℤ).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hℓ).irreducible
  haveI hl : v.asIdeal.LiesOver (Ideal.span {((ℓ : ℕ) : ℤ)}) := by
    refine ⟨hmax.eq_of_le ?_ ?_⟩
    · exact (v.isPrime.comap (algebraMap ℤ (𝓞 K))).ne_top
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 K) ((ℓ : ℕ) : ℤ) ∈ v.asIdeal
      rw [map_natCast]; exact hv
  rw [Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal hℓ] at h
  exact (Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h)

theorem splitIn_of_cls {D : D7} {p : ℕ} (h : D.host.cls p = .splitK) : SplitIn D p := by
  right
  unfold Formalism.BasicNotions.Host.cls primeClass at h
  split_ifs at h with h1 h2 h3 h4 <;> first | exact h4 | cases h

theorem goodLevel {D : D7} {T : Type} {L : LevCh D T} (P : Places L)
    (hsplit : ∀ p ∈ D.host.levelPrimes, D.host.cls p = .splitK) : GoodLevel D (levQ P) := by
  refine ⟨?_, fun p hp hdvd => ?_⟩
  · unfold levQ
    exact Finset.prod_pos fun v _ => pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)) _
  · unfold levQ at hdvd
    obtain ⟨v, hv, hd⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdvd
    have hd' := hp.dvd_of_dvd_pow hd
    rcases P.mem_S0_of_sum_eq.1 hv with rfl | h1
    · rw [eq_of_dvd_absNorm _ (leastSplitAuxiliaryPrimeThetaChain_spec D).1 hp P.basePlace_over_qZero hd']
      exact Or.inr (Formalism.L2.Host.split_prime_jacobi_neg_d D)
    · rcases (S1_mem_OmF D).1 h1 with h | h | h | h
      · rw [eq_of_dvd_absNorm _ (D.host.g_prime 0) hp h hd']
        exact splitIn_of_cls (hsplit _ (D.host.g_level 0))
      · rw [eq_of_dvd_absNorm _ (D.host.g_prime 1) hp h hd']
        exact splitIn_of_cls (hsplit _ (D.host.g_level 1))
      · rw [eq_of_dvd_absNorm _ D.host.pde_prime hp h hd']
        exact splitIn_of_cls (hsplit _ D.host.pde_level.1)
      · rw [eq_of_dvd_absNorm _ D.host.pde'_prime hp h hd']
        exact splitIn_of_cls (hsplit _ D.host.pde_level.2)

theorem twPl_base {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) :
    twPl G μ₀ = ∅ := by
  have hQ : L.Q μ₀ = ∅ := by
    ext PP
    simp only [Finset.notMem_empty, iff_false]
    intro h
    refine ((hL.Q_ram μ₀ PP).2 (Or.inl h)) ?_
    rw [hL.xi_base]
    intro x _
    rfl
  ext w
  simp [twPl, locPl, hQ]

theorem nuH_inv_hasInf_all {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc)
    (t : T) (i j : Fin D.R.m) : (nuH G t i j)⁻¹.HasInf (Formalism.L2.Host.embTau D)
      (fun τ => 2 * ((GlobalTheory.ChiGrid.num D sc.cGap τ).e (j + 1) + GlobalTheory.ChiGrid.cen D sc.cGap τ (D.R.m - i))) := by
  intro k
  have e : nuH G t i j = nuH G μ₀ i j * L.xiH t := by
    simp only [nuH, hL.xi_base, mul_one]; exact mul_div_right_comm _ _ _
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  rw [e, mul_inv, HChar.inf_mul, Units.val_mul, HChar.inf_inv (L.xiH t), Formalism.L2.Host.HChar.inf_eq_one_of_order hn ho k, inv_one,
    Units.val_one, mul_one]
  exact nuH_inv_hasInf hL G i j k

theorem rankV_lt {D : D7} {i j : ℕ} (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : rankV D i j + 1 ≤ bigN D := by
  have hm := D.R.two_le_m
  have e1 : j * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
  have e2 : i * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
  have e3 : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
  simp only [rankV, bigN, Ranks.r]
  omega

theorem bottomRank_sum_le_two_mul_totalRank (D : D7) (i j : Fin D.R.m) : botBig D i j + botSmall D i j ≤ 2 * bigN D := by
  obtain ⟨h1, h2, -⟩ := ranks_exact D i j
  have a1 := rankV_lt (D := D) (i := i + 1) (j := j + 1) (by omega) (by omega)
  have a2 := rankV_lt (D := D) (i := i) (j := j) (by omega) (by omega)
  omega

theorem natAbs_le_maxWt (D : D7) (C : ℝ) (i j : Fin D.R.m) (τ : D.what₂.Tau) :
    max (wtA D C i j τ).natAbs (wtA' D C i j τ).natAbs ≤ maxWt D C := by
  unfold maxWt
  refine le_max_of_le_right ?_
  have := Finset.le_sup (f := fun x : Fin D.R.m × Fin D.R.m × D.what₂.Tau =>
      max (wtA D C x.1 x.2.1 x.2.2).natAbs (wtA' D C x.1 x.2.1 x.2.2).natAbs) (Finset.mem_univ (i, j, τ))
  exact this

theorem n_le_arith {n d ε c e A A' : ℤ} (hd : 0 ≤ d) (hε : ε = 1 ∨ ε = -1) (hc : c = e ∨ c = -e)
    (hw : 2 * n = ε * c - d) (hA : 2 * (A - A') = e - d) : n ≤ |A| + |A'| := by
  have l1 := le_abs_self A
  have l2 := neg_abs_le A
  have l3 := le_abs_self A'
  have l4 := neg_abs_le A'
  rcases hε with rfl | rfl <;> rcases hc with rfl | rfl <;> omega

theorem small_of {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc)
    (t : T) (i j : Fin D.R.m) {δ t0 : ℂ} {Q : ℕ} (X : Pair D ⊤ δ t0 Q) (hd : X.d = botBig D i j + botSmall D i j)
    {χ : HChar D.host.E} (hc : HasChars X χ (nuH G t i j)⁻¹) : X.Small (bigN D) (maxWt D sc.cGap) := by
  refine ⟨hd ▸ bottomRank_sum_le_two_mul_totalRank D i j, fun τ => ?_⟩
  have habs := GlobalTheory.SplitWeight.abs_weight_eq_abs_infType X.W.chV' X.W.ep' _ _ X.W.ep_pm.2 hc.2
    (nuH_inv_hasInf_all hL G t i j) τ
  have hw : 2 * (X.n τ : ℤ) = X.W.ep' * X.W.chV'.n τ - ((botBig D i j + botSmall D i j : ℕ) : ℤ) := by
    rw [← hd]; exact X.wt τ
  have hn := n_le_arith (Nat.cast_nonneg _) X.W.ep_pm.2 (abs_eq_abs.1 habs) hw (two_mul_wtA_sub D sc.cGap i j τ)
  have hB := natAbs_le_maxWt D sc.cGap i j τ
  have hB1 := (le_max_left _ _).trans hB
  have hB2 := (le_max_right _ _).trans hB
  have c1 : ((wtA D sc.cGap i j τ).natAbs : ℤ) = |wtA D sc.cGap i j τ| := Int.natCast_natAbs _
  have c2 : ((wtA' D sc.cGap i j τ).natAbs : ℤ) = |wtA' D sc.cGap i j τ| := Int.natCast_natAbs _
  have hB1' : ((wtA D sc.cGap i j τ).natAbs : ℤ) ≤ maxWt D sc.cGap := by exact_mod_cast hB1
  have hB2' : ((wtA' D sc.cGap i j τ).natAbs : ℤ) ≤ maxWt D sc.cGap := by exact_mod_cast hB2
  have n_le : (X.n τ : ℤ) ≤ 2 * maxWt D sc.cGap := by linarith
  exact_mod_cast n_le

theorem botSmall_holds : BotSmall := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ hL G => ⟨?_, ?_, ?_⟩⟩⟩
  · obtain ⟨⟨Pm, -, -⟩, -⟩ := hR.size
    exact goodLevel G.pl Pm.level_split
  · exact twPl_base G hL
  · intro δ t0 Q P P' t i j 𝔪 h
    exact ⟨small_of hL G t i j P h.rank.2.2.1 h.chars,
      small_of hL G t i j P' (h.rank.2.2.2.trans h.rank.2.2.1) h.chars'⟩

end GlobalTheory.SqTop.BotSmallProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqOnMirabolicOfSlicesFinitePlacesStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_on_mirabolic_of_slices_finitePlaces : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ) (𝒲 : Submodule ℂ (GA E (m + 1) → ℂ)), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ W ∈ 𝒲, ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ W ∈ 𝒲, ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, (fun g => W (g * h)) ∈ 𝒲) → (∀ W ∈ 𝒲, ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, W (g * finGL E (m + 1) u) = W g) → (∀ q ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GeneralLinearGroup.map (pInf E) q = 1 → ∃ W ∈ 𝒲, ∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) → W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y)) → ∃ W ∈ 𝒲, ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), W p = b p := by
  first | (exact @GlobalTheory.JSW.MirPatch.exists_eq_on_mirS_of_slices) | (exact GlobalTheory.JSW.MirPatch.exists_eq_on_mirS_of_slices) | (intros; apply GlobalTheory.JSW.MirPatch.exists_eq_on_mirS_of_slices  <;> assumption)
end

