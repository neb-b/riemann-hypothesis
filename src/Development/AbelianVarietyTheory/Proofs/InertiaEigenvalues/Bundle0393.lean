module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0018
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0364
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0363
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinLatticeFrameOfLinkedPreframe
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
namespace GlobalTheory.BKLim

theorem frame_of_links : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val) (P : Pre bk N d fun g => (ρ g).val) (r : ℕ), (∀ n, ∃ m, n ≤ m ∧ Link bk P.T (F m).T (tw.Pi m) n r) → ∃ F₀ : Frame bk N d fun g => (ρ g).val, F₀.toPre = P := by
  intro l _ K bk d N ρ tw F P r hL
  obtain ⟨u, hu⟩ := P.unit
  obtain ⟨Ti, hT1, hT2⟩ : ∃ Ti : Matrix (Fin d) (Fin d) (WCb l), P.T * Ti = 1 ∧ Ti * P.T = 1 :=
    ⟨↑u⁻¹, by rw [← hu]; exact u.mul_inv, by rw [← hu]; exact u.inv_mul⟩
  have key : ∀ (g : ↥(GK K)) (i j : Fin d), ∃ a : Ainf l,
      (Ti * zW (ρ g).val * P.T.map (galW l (g : GQ l))) i j
        = inclW l (1 * a) := by
    intro g i j
    refine _root_.GlobalTheory.AinfSat.mem_ideal_of_saturated l 1 (by simp) r _ ?_
    intro n
    obtain ⟨m, hnm, R, G, hc, hd⟩ := hL n
    obtain ⟨σ, hσ⟩ : ∃ σ : WCb l →+* WCb l, ∀ x, σ x = galW l (g : GQ l) x := ⟨((galW l (g : GQ l)).toRingEquiv : WCb l →+* WCb l), fun _ => rfl⟩
    have hσf : (⇑(galW l (g : GQ l)) : WCb l → WCb l) = ⇑σ := funext fun x => (hσ x).symm
    set π := Ideal.Quotient.mk (Ideal.span {((l : WCb l) ^ n)}) with hπ
    have hq : ∀ x y : WCb l, (l : WCb l) ^ n ∣ x - y → π x = π y := fun x y h =>
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h)
    have hM : ∀ {a b : Type} (A B : Matrix a b (WCb l)),
        (∀ i j, (l : WCb l) ^ n ∣ (A - B) i j) → A.map π = B.map π := fun A B h => by
      ext i j; exact hq _ _ (by simpa using h i j)
    have hσd : ∀ x : WCb l, (l : WCb l) ^ n ∣ x → (l : WCb l) ^ n ∣ σ x := fun x ⟨y, hy⟩ =>
      ⟨σ y, by rw [hy, map_mul, map_pow, map_natCast]⟩
    have hσz : ∀ {a b : Type} (M : Matrix a b ℤ_[l]), (zW M).map σ = zW M := fun M => by
      ext i j; simp [zW, hσ]
    have hMM : ∀ {a b b' c : Type} [Fintype b] [Fintype b'] (A : Matrix a b (WCb l)) (B : Matrix b c (WCb l))
        (C : Matrix a b' (WCb l)) (D : Matrix b' c (WCb l)),
        (∀ i j, (l : WCb l) ^ n ∣ (A * B - C * D) i j) → A.map π * B.map π = C.map π * D.map π := by
      intro a b b' c _ _ A B C D h
      rw [← Matrix.map_mul, ← Matrix.map_mul]; exact hM _ _ h
    set T' := (F m).T
    set ε' := (F m).ε g
    set Pi := tw.Pi m
    have Ga := (F m).gal g
    rw [hσf] at Ga
    rw [hσf]
    have E1 : (zW Pi).map π * T'.map π = P.T.map π * (R.map bk.evW).map π := by
      rw [← Matrix.map_mul, ← Matrix.map_mul]; exact hM _ _ hc
    have E1σ : (zW Pi).map π * (T'.map σ).map π = (P.T.map σ).map π * ((R.map bk.evW).map σ).map π := by
      rw [← Matrix.map_mul, ← Matrix.map_mul]
      apply hM
      intro i j
      have h1 : zW Pi * T'.map σ - P.T.map σ * (R.map bk.evW).map σ = (zW Pi * T' - P.T * R.map bk.evW).map σ := by
        rw [Matrix.map_sub _ (map_sub σ), Matrix.map_mul, Matrix.map_mul, hσz]
      rw [h1, Matrix.map_apply]; exact hσd _ (hc i j)
    have E2 : (zW Pi).map π * (zW (tw.ρ' m g).val).map π = (zW (ρ g).val).map π * (zW Pi).map π := by
      apply hMM
      intro i j
      have h1 : zW Pi * zW (tw.ρ' m g).val - zW (ρ g).val * zW Pi = zW (Pi * (tw.ρ' m g).val - (ρ g).val * Pi) := by
        simp only [zW]; rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul]
      rw [h1]
      have h2 := map_dvd (algebraMap ℤ_[l] (WCb l)) ((pow_dvd_pow (l : ℤ_[l]) hnm).trans ((tw.onto m).equi g i j))
      simpa [zW] using h2
    have E3 : ((R.map bk.evW).map σ).map π * ((G.map bk.evW).map σ).map π
        = (((l : WCb l) ^ r) • (1 : Matrix (Fin d) (Fin d) (WCb l))).map π := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul]
      apply hM
      intro i j
      have h1 : (((R * G).map bk.evW).map σ - ((l : WCb l) ^ r) • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j
          = σ (bk.evW ((R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) bk.S)) i j)) := by
        simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, map_sub]
        split_ifs <;> simp
      rw [h1]
      exact hσd _ (by simpa using map_dvd bk.evW (hd i j))
    have He : P.T.map π * ((Ti * zW (ρ g).val * P.T.map σ).map π) = (zW (ρ g).val).map π * (P.T.map σ).map π := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hT1, Matrix.one_mul]
    have GaP : (zW (tw.ρ' m g).val).map π * (T'.map σ).map π = T'.map π * (ε'.map (inclW l)).map π := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, Ga]
    have C1 : P.T.map π * ((Ti * zW (ρ g).val * P.T.map σ).map π * ((R.map bk.evW).map σ).map π)
        = P.T.map π * ((R.map bk.evW).map π * (ε'.map (inclW l)).map π) := by
      calc P.T.map π * ((Ti * zW (ρ g).val * P.T.map σ).map π * ((R.map bk.evW).map σ).map π)
          = (P.T.map π * (Ti * zW (ρ g).val * P.T.map σ).map π) * ((R.map bk.evW).map σ).map π := (Matrix.mul_assoc _ _ _).symm
        _ = (zW (ρ g).val).map π * ((P.T.map σ).map π * ((R.map bk.evW).map σ).map π) := by rw [He, Matrix.mul_assoc]
        _ = (zW (ρ g).val).map π * ((zW Pi).map π * (T'.map σ).map π) := by rw [E1σ]
        _ = ((zW Pi).map π * (zW (tw.ρ' m g).val).map π) * (T'.map σ).map π := by rw [E2, Matrix.mul_assoc]
        _ = (zW Pi).map π * (T'.map π * (ε'.map (inclW l)).map π) := by rw [Matrix.mul_assoc, GaP]
        _ = P.T.map π * ((R.map bk.evW).map π * (ε'.map (inclW l)).map π) := by rw [← Matrix.mul_assoc, E1, Matrix.mul_assoc]
    have hTi : Ti.map π * P.T.map π = 1 := by
      rw [← Matrix.map_mul, hT2, Matrix.map_one _ (map_zero _) (map_one _)]
    have C2 : (Ti * zW (ρ g).val * P.T.map σ).map π * ((R.map bk.evW).map σ).map π
        = (R.map bk.evW).map π * (ε'.map (inclW l)).map π := by
      calc _ = (Ti.map π * P.T.map π) *
            ((Ti * zW (ρ g).val * P.T.map σ).map π * ((R.map bk.evW).map σ).map π) := by rw [hTi, Matrix.one_mul]
        _ = _ := by rw [Matrix.mul_assoc, C1, ← Matrix.mul_assoc, hTi, Matrix.one_mul]
    have C3 : (Ti * zW (ρ g).val * P.T.map σ).map π * (((R.map bk.evW).map σ).map π * ((G.map bk.evW).map σ).map π)
        = (R.map bk.evW).map π * (ε'.map (inclW l)).map π * ((G.map bk.evW).map σ).map π := by
      rw [← Matrix.mul_assoc, C2]
    rw [E3] at C3
    have hR : (R.map bk.ev).map (inclW l) = R.map bk.evW := by ext; rfl
    have hG : (G.map fun x => Per.σA (g : GQ l) (bk.ev x)).map (inclW l) = (G.map bk.evW).map σ := by
      ext; simp [BK.evW, hσ, galW_inclW]
    have hY : ((R.map bk.ev * ε' * G.map fun x => Per.σA (g : GQ l) (bk.ev x)).map (inclW l)).map π
        = (R.map bk.evW).map π * (ε'.map (inclW l)).map π * ((G.map bk.evW).map σ).map π := by
      simp only [Matrix.map_mul, hR, hG]
    refine ⟨(R.map bk.ev * ε' * G.map fun x => Per.σA (g : GQ l) (bk.ev x)) i j, ?_⟩
    have C4 : (((l : WCb l) ^ r) • (Ti * zW (ρ g).val * P.T.map σ)).map π
        = ((R.map bk.ev * ε' * G.map fun x => Per.σA (g : GQ l) (bk.ev x)).map (inclW l)).map π := by
      rw [hY, ← C3, ← Matrix.map_mul, Matrix.mul_smul, mul_one]
    have C5 := congrFun (congrFun C4 i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at C5
    rw [one_mul]
    exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 C5)
  choose ε hε using key
  refine ⟨{ toPre := P, ε := fun g => Matrix.of (ε g), gal := fun g => ?_ }, rfl⟩
  have h1 : (Matrix.of (ε g)).map (inclW l) = Ti * zW (ρ g).val * P.T.map (galW l (g : GQ l)) := by
    ext i j; rw [Matrix.map_apply, Matrix.of_apply, hε g i j, one_mul]
  show zW (ρ g).val * P.T.map (galW l (g : GQ l)) = P.T * (Matrix.of (ε g)).map (inclW l)
  rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hT1, Matrix.one_mul]

end GlobalTheory.BKLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivMapLattice
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
open scoped TensorProduct

namespace GlobalTheory.TwistChoice

section Semilinear

theorem exists_equiv_map_lattice {O K U U' : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [AddCommGroup U] [Module K U] [Module O U] [IsScalarTower O K U]
    [AddCommGroup U'] [Module K U'] [Module O U'] [IsScalarTower O K U']
    (A : Submodule O U) (B : Submodule O U') [A.IsFullLattice K] [B.IsFullLattice K]
    (h : Module.finrank K U = Module.finrank K U') :
    ∃ g : U ≃ₗ[K] U', A.map (g.toLinearMap.restrictScalars O) = B := by
  have key : ∀ {V : Type} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (C : Submodule O V)
      [C.IsFullLattice K], ∃ c : Module.Basis (Fin (Module.finrank K V)) K V, Submodule.span O (Set.range c) = C := by
    intro V _ _ _ _ C _
    haveI := Submodule.IsLattice.free K C
    haveI := Submodule.IsLattice.finite K C
    let c₀ := Module.finBasis O C
    let c₁ := c₀.extendOfIsFullLattice K
    have hn : Module.finrank K V = Module.finrank O C := by
      rw [Module.finrank_eq_card_basis c₁, Fintype.card_fin]
    refine ⟨c₁.reindex (finCongr hn.symm), ?_⟩
    rw [Module.Basis.range_reindex]
    have h1 : Set.range c₁ = C.subtype '' Set.range c₀ := by
      rw [← Set.range_comp]
      congr 1
      funext i
      exact c₀.extendOfIsFullLattice_apply K i
    rw [h1, ← Submodule.map_span, c₀.span_eq, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨a, ha⟩ := key A
  obtain ⟨b, hb⟩ := key B
  refine ⟨a.equiv b (finCongr h), ?_⟩
  rw [← ha, ← hb, Submodule.map_span, ← Set.range_comp, ← (finCongr h).surjective.range_comp b]
  congr 2
  funext i
  exact Module.Basis.equiv_apply _ _ _ _

theorem exists_semilinear {L V O K U : Type} [Field L] [AddCommGroup V] [Module L V] [Module.Finite L V]
    [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup U] [Module K U] [Module O U] [IsScalarTower O K U] (e : L →+* K)
    (S : Set V) (hS : S.Finite) (hspan : Submodule.span L S = ⊤) (B : Submodule O U) [B.IsFullLattice K]
    (h : Module.finrank L V = Module.finrank K U) :
    ∃ f : V →ₛₗ[e] U,
      (∀ (ι : Type) (b : Module.Basis ι L V), LinearIndependent K (fun i => f (b i)) ∧
        Submodule.span K (Set.range fun i => f (b i)) = ⊤) ∧ Submodule.span O (f '' S) = B := by
  classical
  let b₀ := Module.finBasis L V
  let f₀ : V →ₛₗ[e] (Fin (Module.finrank L V) → K) :=
    { toFun := fun x i => e (b₀.repr x i)
      map_add' := fun x y => by funext i; simp
      map_smul' := fun c x => by funext i; simp }
  have hf₀ : ∀ T : Set V, Submodule.span L T = ⊤ → Submodule.span K (f₀ '' T) = ⊤ := by
    intro T hT
    have h1 : ∀ x, f₀ x ∈ Submodule.span K (f₀ '' T) := fun x => by
      have hx : x ∈ Submodule.span L T := hT ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
      | smul c y _ hy => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
    apply eq_top_iff.mpr
    rw [← (Pi.basisFun K (Fin (Module.finrank L V))).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have heq : (Pi.basisFun K (Fin (Module.finrank L V))) i = f₀ (b₀ i) := by
      ext j
      simp [f₀, Pi.basisFun_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]
    rw [heq]
    exact h1 (b₀ i)
  let A : Submodule O (Fin (Module.finrank L V) → K) := Submodule.span O (f₀ '' S)
  haveI : A.IsFullLattice K :=
    { toIsLattice := Submodule.IsLattice.of_fg _ (Submodule.fg_span (hS.image _))
      span_eq_top := by rw [show A = Submodule.span O (f₀ '' S) from rfl, Submodule.span_span_of_tower, hf₀ S hspan] }
  obtain ⟨g, hg⟩ := exists_equiv_map_lattice (K := K) A B (by rw [← h]; simp)
  refine ⟨g.toLinearMap.comp f₀, fun ι b => ?_, ?_⟩
  · haveI : Finite ι := Module.Finite.finite_basis b
    haveI := Fintype.ofFinite ι
    have h1 : Submodule.span K (Set.range fun i => (g.toLinearMap.comp f₀) (b i)) = ⊤ := by
      have h2 : (Set.range fun i => (g.toLinearMap.comp f₀) (b i)) = g.toLinearMap '' (f₀ '' Set.range b) := by
        rw [← Set.range_comp, ← Set.range_comp]; rfl
      rw [h2, ← Submodule.map_span, hf₀ _ b.span_eq, Submodule.map_top]
      exact g.range
    exact ⟨linearIndependent_of_top_le_span_of_card_eq_finrank h1.ge
      (by rw [← h, Module.finrank_eq_card_basis b]), h1⟩
  · rw [← hg, Submodule.map_span, Set.image_image]
    rfl

theorem form_gen {L V M ι : Type} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] {σ : L →+* ℂ} (j : V →ₛₗ[σ] M) (b : Module.Basis ι L V)
    (hb : LinearIndependent ℂ (fun i => j (b i)) ∧ Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤)
    (T : Finset M) (hT : Submodule.span ℂ (T : Set M) = ⊤) (hsub : ∀ x ∈ T, x ∈ Set.range j) :
    Module.Finite L V ∧ {x | j x ∈ T}.Finite ∧ Submodule.span L {x | j x ∈ T} = ⊤ := by
  haveI : Finite ι := hb.1.finite
  haveI := Fintype.ofFinite ι
  let B : Module.Basis ι ℂ M := Module.Basis.mk hb.1 hb.2.ge
  have hB : ∀ i, B i = j (b i) := fun i => by simp [B]
  have key : ∀ l : V →ₗ[L] L, ∃ l' : M →ₗ[ℂ] ℂ, ∀ x, l' (j x) = σ (l x) := fun l => by
    refine ⟨B.constr ℂ fun i => σ (l (b i)), fun x => ?_⟩
    conv_lhs => rw [← b.sum_repr x]
    conv_rhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, ← hB, Module.Basis.constr_basis, smul_eq_mul, map_mul, RingHom.id_apply]
  have hinj : Function.Injective j := fun x y hxy => by
    refine b.ext_elem fun i => σ.injective ?_
    obtain ⟨l', hl'⟩ := key (b.coord i)
    have h1 := hl' x
    rw [hxy, hl' y] at h1
    exact h1.symm
  refine ⟨Module.Finite.of_basis b, T.finite_toSet.preimage hinj.injOn, ?_⟩
  by_contra hne
  obtain ⟨l, hl0, hl⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨l', hl'⟩ := key l
  have h1 : l' = 0 := by
    rw [← LinearMap.ker_eq_top, eq_top_iff, ← hT, Submodule.span_le]
    intro y hy
    obtain ⟨x, rfl⟩ := hsub y hy
    have hx : l x = 0 := hl (Submodule.subset_span hy)
    show l' (j x) = 0
    rw [hl', hx, map_zero]
  refine hl0 (LinearMap.ext fun x => σ.injective ?_)
  rw [← hl', h1]
  simp

theorem baseChange_lattice {A B V : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B)) [AddCommGroup V] [Module (FractionRing A) V] [Module A V]
    [IsScalarTower A (FractionRing A) V] (Λ : Submodule A V) (hfg : Λ.FG)
    (hspan : Submodule.span (FractionRing A) (Λ : Set V) = ⊤) :
    Module.finrank (FractionRing B) (FractionRing B ⊗[A] V) = Module.finrank (FractionRing A) V ∧
      (Submodule.span B ((TensorProduct.mk A (FractionRing B) V 1) '' (Λ : Set V))).IsFullLattice (FractionRing B) := by
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hinj
  letI : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra A (FractionRing B)
  haveI : IsScalarTower A (FractionRing A) (FractionRing B) := FractionRing.isScalarTower_liftAlgebra A (FractionRing B)
  refine ⟨?_, { toIsLattice := Submodule.IsLattice.of_fg _ ?_, span_eq_top := ?_ }⟩
  · rw [← (TensorProduct.AlgebraTensorModule.cancelBaseChange A (FractionRing A) (FractionRing B) (FractionRing B) V).finrank_eq,
      Module.finrank_baseChange, (NChoice.fracEquiv A V).finrank_eq]
  · obtain ⟨T, rfl⟩ := hfg
    rw [← Submodule.map_coe, ← Submodule.span_image, Submodule.span_span_of_tower]
    exact Submodule.fg_span (T.finite_toSet.image _)

  · rw [Submodule.span_span_of_tower, eq_top_iff]
    rintro x -
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add y z hy hz => exact Submodule.add_mem _ hy hz
    | tmul a v =>
      obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors A) (FractionRing A) (Λ : Set V) v
        (hspan ▸ Submodule.mem_top)
      rw [Submodule.span_eq] at hd
      have hd0 : algebraMap A (FractionRing B) d ≠ 0 :=
        (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A (FractionRing B))).2 (nonZeroDivisors.coe_ne_zero d)
      have h1 : a ⊗ₜ[A] v = (a * (algebraMap A (FractionRing B) d)⁻¹) • ((1 : FractionRing B) ⊗ₜ[A] ((d : A) • v)) := by
        rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def (d : A), mul_one, smul_eq_mul,
          mul_assoc, inv_mul_cancel₀ hd0, mul_one]
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hd, rfl⟩)

end Semilinear

section Series

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (E : IntegralHeckeForms.ExpDat Y)

theorem twOK_one (i : X.Tw) (k : ℕ) : IntegralHeckeForms.TwOK i k ∅ (1 : G D.host.E N.Om →* (X.Ok i k)ˣ) := by
  refine ⟨by simp, by simp, by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ, fun g g' _ => by simp, fun g => Subgroup.one_mem _, fun v A _ => by simp,
    fun v _ A _ σ _ => rfl⟩

theorem th_fg (h : IntegralHeckeForms.admT4 Y E) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool) :
    (IntegralHeckeForms.Th Y i j b (IntegralHeckeForms.SgJ Y E i j b)).FG := by
  have h1 := h i hi j hj b 0 ∅ 1 (twOK_one i 0) _ subset_rfl
  haveI := X.Ok_fin i 0
  haveI : FaithfulSMul (X.O i) (X.Ok i 0) := (faithfulSMul_iff_algebraMap_injective _ _).2 (X.Ok_inj i 0)
  haveI : Module.FaithfullyFlat (X.O i) (X.Ok i 0) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have h2 : (((Y.MtLat i j b 0 ∅ 1).map (Y.thP i j b 0 ∅ 1)).restrictScalars (X.O i)).FG :=
    ((Y.MtLat_fg i j b 0 ∅ 1).map _).restrictScalars
  let m := TensorProduct.mk (X.O i) (X.Ok i 0) (Y.Fm i j b) 1
  refine Submodule.fg_of_fg_map_injective m (Module.FaithfullyFlat.tensorProduct_mk_injective _) (h2.of_le ?_)
  rw [IntegralHeckeForms.Th, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  refine h1 (Submodule.subset_span (Set.mem_iUnion₂.2 ⟨a, ha, ?_⟩))
  rw [Y.thPsi_one]
  rfl

theorem exists_basisOf (i : X.Tw) (j : ℕ) (b : Bool) (Sg : Set (Y.Dat i j b)) (h : (IntegralHeckeForms.Th Y i j b Sg).FG) :
    ∃ S : Finset (Y.Dat i j b), IntegralHeckeForms.BasisOf Y i j b Sg S := by
  classical
  have hr : Submodule.span (X.O i) (Set.range fun a : Sg => IntegralHeckeForms.AO Y i j b (Y.th i j b a)) =
      (IntegralHeckeForms.Th Y i j b Sg).map (IntegralHeckeForms.AO Y i j b) := by
    rw [IntegralHeckeForms.Th, Submodule.map_span, Set.image_image, Set.image_eq_range]
  obtain ⟨S, h1, h2⟩ := exists_subbasis (X.O i) (Y.Fm i j b) Sg (fun a => IntegralHeckeForms.AO Y i j b (Y.th i j b a))
    (fun c w hc hw => by
      rw [← algebraMap_smul (FractionRing (X.O i)) c w, smul_eq_zero] at hw
      exact hw.resolve_left ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hc))
    (hr ▸ h.map _)
  refine ⟨S.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨a', -, rfl⟩ := Finset.mem_map.1 ha
    exact a'.2
  · let e : S ≃ (S.map (Function.Embedding.subtype (· ∈ Sg)) : Finset _) :=
      Equiv.ofBijective (fun a => ⟨a.1.1, Finset.mem_map.2 ⟨a.1, a.2, rfl⟩⟩)
        ⟨fun a a' h => Subtype.ext (Subtype.ext (Subtype.mk.inj h)), fun ⟨y, hy⟩ => by
          obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hy
          exact ⟨⟨a, ha⟩, rfl⟩⟩
    exact (linearIndependent_equiv e).1 h1
  · rw [← hr, ← h2, Finset.coe_map, Set.image_image]
    rfl

end Series

end GlobalTheory.TwistChoice

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEvaluationConvergentSeriesBcrisStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_evaluation_convergent_series_Bcris : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∃ J, IsEval I β J := by
  first | exact @GlobalTheory.HWL.BanachEval.exists_eval | exact GlobalTheory.HWL.BanachEval.exists_eval | (intros; apply GlobalTheory.HWL.BanachEval.exists_eval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExtFixing
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.HodgeAt

theorem phiS_idem : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K L : FinExt l) [FiniteDimensional ℚ_[l] ↥K.1] (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (σ : GQ l), (∀ x : ↥K.1, σ ((τ x : ↥L.1) : Om l) = (x : Om l)) → phiS P σ L (GlobalTheory.DRFil.idem P.R.BdR τ) = 1 := by
  intro l _ P K L _ τ σ hσ
  obtain ⟨n, a, c, h, h1⟩ := GlobalTheory.DRFil.idem_repr P.R.BdR τ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum]
  simp only [phiS_tmul]
  have hc : ∀ i, algebraMap ↥K.1 P.R.BdR (c i) = algebraMap (Om l) P.R.BdR ((c i : ↥K.1) : Om l) := fun i => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hc, ← map_mul, ← map_sum]
  have : ∑ i, σ ((a i : ↥L.1) : Om l) * ((c i : ↥K.1) : Om l) = σ (((∑ i, a i * τ (c i) : ↥L.1)) : Om l) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [IntermediateField.coe_sum, IntermediateField.coe_mul, map_sum, map_mul, hσ]
  rw [this, h1]
  simp

theorem phiS_mem_Fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K L : FinExt l) (σ : GQ l) (n : ℤ) (r : ↥L.1 ⊗[ℚ_[l]] P.R.BdR), r ∈ FilV (P.PD K) (LL := ↥L.1) (V := ↥L.1) n → phiS P σ L r ∈ (P.PD K).Fil n := by
  intro l _ P AI T K L σ n r hr
  have h0 : ∀ x : Om l, algebraMap (Om l) P.R.BdR x ∈ (P.PD K).Fil 0 := by
    intro x
    rw [T.fil]
    obtain ⟨y, hy, -⟩ := T.om x
    rw [hy]
    exact ((GlobalTheory.MemLoc.filD_laws l).2.2.2.2.2.2 0 y).2 (GlobalTheory.MemLoc.FilSeed.mem_filtration_zero' y)
  refine GlobalTheory.DRFil.FilV_induction (P.PD K) (p := fun r => phiS P σ L r ∈ (P.PD K).Fil n) ?_ ?_ ?_ hr
  · simp
  · intro c b hb
    rw [phiS_tmul]
    simpa using (P.PD K).Fil_mul 0 n _ _ (h0 _) hb
  · intro x y hx hy
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hx hy

end GlobalTheory.HodgeAt

namespace GlobalTheory.HodgeAt

theorem exists_ext_fixing : ∀ (l : ℕ) [Fact l.Prime] (K L : FinExt l) (σ : GQ l), ∃ K' : FinExt l, K.1 ≤ K'.1 ∧ ∀ g ∈ GK K', ∀ y : ↥L.1, g (σ (y : Om l)) = σ (y : Om l) := by
  intro l _ K L σ
  haveI := K.2
  haveI := L.2
  haveI : FiniteDimensional ℚ_[l] ↥(L.1.map (σ : Om l →ₐ[ℚ_[l]] Om l)) :=
    LinearEquiv.finiteDimensional (IntermediateField.equivMap L.1 (σ : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv
  refine ⟨⟨K.1 ⊔ L.1.map (σ : Om l →ₐ[ℚ_[l]] Om l), IntermediateField.finiteDimensional_sup _ _⟩, le_sup_left, ?_⟩
  intro g hg y
  have hmem : σ (y : Om l) ∈ K.1 ⊔ L.1.map (σ : Om l →ₐ[ℚ_[l]] Om l) :=
    le_sup_right (a := K.1) ((IntermediateField.mem_map _).2 ⟨y, y.2, rfl⟩)
  exact (mem_fixingSubgroup_iff _).1 hg _ hmem

end GlobalTheory.HodgeAt

namespace GlobalTheory.HodgeAt

theorem exists_xi_pow_mul : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l) (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (K : FinExt l) (k : ℤ) (q p : ℕ), k + q = p → ∀ x ∈ (P.PD K).Fil k, ∃ z : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ q * T.eD x = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ p * z) := by
  intro l _ P AI T C ξ hξ K k q p hkp x hx
  obtain ⟨hP, -, -, -, -, hshift, -⟩ := GlobalTheory.MemLoc.seed_fil l C ξ hξ
  rw [T.fil] at hx
  have hy := (hshift k q (T.eD x)).2 hx
  rw [hkp] at hy
  obtain ⟨y, hye⟩ := (GlobalTheory.MemLoc.mem_FilD_iff_xi_pow l C.ε (GlobalTheory.MemLoc.core_isEps l C) p _).1 hy
  have h0 : (-(p : ℤ)).toNat = 0 := by omega
  rw [h0, pow_zero, mul_one, Int.toNat_natCast] at hye
  have hz : aDp l (xi C.ε) ^ p * y ∈ Per.FilP l p :=
    ((GlobalTheory.MemLoc.filtration_eq_xi_pow l C.ε (GlobalTheory.MemLoc.core_isEps l C)).1 p _).2 (dvd_mul_right _ _)
  rw [hP, Ideal.mem_span_singleton'] at hz
  obtain ⟨z', hz'⟩ := hz
  refine ⟨z', ?_⟩
  rw [mul_comm (aDp l ξ ^ p) z', hz', hye]

end GlobalTheory.HodgeAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiltrationAdaptedBasisOfSubspaceStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_filtration_adapted_basis_of_subspace : ∀ {k M : Type} [Field k] [AddCommGroup M] [Module k M] (D : Submodule k M) [FiniteDimensional k D] (F : ℤ → Submodule k M), Antitone F → (∀ x ∈ D, ∃ a, x ∈ F a) → (∀ x ∈ D, (∀ a, x ∈ F a) → x = 0) → ∃ (b : Module.Basis (Fin (Module.finrank k D)) k D) (h : Fin (Module.finrank k D) → ℤ), (∀ j, (b j : M) ∈ F (h j) ∧ (b j : M) ∉ F (h j + 1)) ∧ ∀ (a : ℤ) (x : D), (x : M) ∈ F a → ∀ j, b.repr x j ≠ 0 → a ≤ h j := by
  first | exact @GlobalTheory.AdaptedBasis.exists_adapted_basis | exact GlobalTheory.AdaptedBasis.exists_adapted_basis | (intros; apply GlobalTheory.AdaptedBasis.exists_adapted_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetPrimePowTorsionQuotientStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_primePow_torsion_quotient : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ k : ℕ, ∃ Es : Finset (LL ⧸ LinearMap.range (Algebra.linearMap O LL)), ∀ e, ((l : ℕ) : O) ^ k • e = 0 → e ∈ Es := by
  first | exact @GlobalTheory.GoodCoeff.exists_finset_pow_torsion | exact GlobalTheory.GoodCoeff.exists_finset_pow_torsion | (intros; apply GlobalTheory.GoodCoeff.exists_finset_pow_torsion <;> assumption)
end

