module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0614
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0610
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0595
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0333
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermUnipotentIntegralVariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0335
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLeviParabolicFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0462
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0347
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0337
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0341
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0357
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0354
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0579
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0345
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0017
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0634
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitOfRetract
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0645
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0644
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0648
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0603
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0455
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0635
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0565
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0476
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationCovarianceLevi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0492
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0504
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0464
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0643
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechHodgeDegenerationNatural
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section
namespace GlobalTheory.CompanionTheory.OmGlobSite

variable {K : Type} [Field K]

theorem vk_cover {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a : ℕ) (T : (KC q U a).FullSubcategory) :
    ∃ α, Vk q U a α T := by
  obtain ⟨-, V, ⟨α, rfl⟩, h⟩ := T.property
  exact ⟨α, h⟩

theorem cov_sSup {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) : sSup (Set.range U.U) = ⊤ := by
  rw [sSup_range]
  exact U.cover

def rho {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a n : ℕ) :
    HT.Hdg q a n ≃ₗ[K] CH.H (Fk q U a) n :=
  LinearEquiv.ofBijective ((CH.Mor.restrict (HT.grT (smFun X q) a) (KC q U a).ι).pull n)
    (GlobalTheory.CompanionTheory.OmLoc.grT_restrict_bijective q _ (cov_sSup q U) a (a + 1) (Nat.lt_succ_self a) n)

theorem rho_pull {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (a n : ℕ)
    (hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T)) (x : HT.Hdg p a n) :
    rho q U a n (HT.pullH u hu a n x) =
      (morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).pull n (rho p W a n x) := by
  have h1 := (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id K) (pullM u hu a)
    (CH.Mor.restrict (HT.grT (smFun X q) a) (KC q U a).ι) n x).1
  have h2 := (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id K)
    (CH.Mor.restrict (HT.grT (smFun Y p) a) (KC p W a).ι)
    (morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG) n x).1
  change (CH.Mor.restrict (HT.grT (smFun X q) a) (KC q U a).ι).pull n ((pullM u hu a).pull n x) =
    (morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).pull n
      ((CH.Mor.restrict (HT.grT (smFun Y p) a) (KC p W a).ι).pull n x)
  rw [← h1, ← h2]
  rfl

theorem glob_site : ∀ (K : Type) [Field K] [CharZero K],
    ∃ e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (U : Cov q) (a j : ℕ),
      HT.Hdg q a (a + j) ≃ₗ[K] (CrystallineSemistableComparison.Pb.cechH (Fk q U a) (Vk q U a) a).cx.H j,
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [Smooth q] [Smooth p]
      (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι) (a : ℕ)
      (hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T))
      (hτ : ∀ α T, Vk q U a α T → Vk p W a (τ α) ((morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).G.obj T))
      (j : ℕ) (c : (CrystallineSemistableComparison.Pb.cechH (Fk p W a) (Vk p W a) a).X j) (h0 : (CrystallineSemistableComparison.Pb.cechH (Fk p W a) (Vk p W a) a).cx.d j c = 0)
      (h1 : (CrystallineSemistableComparison.Pb.cechH (Fk q U a) (Vk q U a) a).cx.d j (fun i =>
        (morU (morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG) (U := capT (Vk p W a) (τ ∘ i))
          (U' := capT (Vk q U a) i) fun T hT k => hτ (i k) T (hT k)).pull a (c (τ ∘ i))) = 0),
      HT.pullH u hu a (a + j) ((e p W a j).symm ((CrystallineSemistableComparison.Pb.cechH (Fk p W a) (Vk p W a) a).cx.cls c h0)) =
        (e q U a j).symm ((CrystallineSemistableComparison.Pb.cechH (Fk q U a) (Vk q U a) a).cx.cls _ h1) := by
  intro K _ _
  obtain ⟨E, hE⟩ := GlobalTheory.T.cech_hodge_to_cohomology_iso K
  refine ⟨fun q _ U a j => (rho q U a (a + j)).trans
      (E (Fk q U a) (Vk q U a) (_root_.GlobalTheory.CompanionTheory.OmGlob.vk_cosieve q U a) (vk_cover q U a) a
        (fun n i r hr => GlobalTheory.T.cover_intersection_graded_vanish q U a n i r hr) j), ?_⟩
  intro X Y q p _ _ u hu U W τ a hG hτ j c h0 h1
  dsimp only
  rw [LinearEquiv.symm_trans_apply, LinearEquiv.symm_trans_apply]
  apply (rho q U a (a + j)).injective
  rw [LinearEquiv.apply_symm_apply, rho_pull q p u hu U W a (a + j) hG, LinearEquiv.apply_symm_apply]
  exact hE _ _ _ _ (_root_.GlobalTheory.CompanionTheory.OmGlob.vk_cosieve p W a) (vk_cover p W a) (_root_.GlobalTheory.CompanionTheory.OmGlob.vk_cosieve q U a) (vk_cover q U a) a
    (fun n i r hr => GlobalTheory.T.cover_intersection_graded_vanish p W a n i r hr) (fun n i r hr => GlobalTheory.T.cover_intersection_graded_vanish q U a n i r hr)
    (morU (pullM u hu a) hG) τ hτ j c h0 h1

end GlobalTheory.CompanionTheory.OmGlobSite
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermFiniteOfSmaller
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CTFin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

def leftN (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) : Submodule ℂ (Sm E (r + s)) where
  carrier := {F | ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g}
  add_mem' := fun {F G} hF hG x g => by
    change F.1 _ + G.1 _ = F.1 _ + G.1 _
    rw [hF, hG]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c F hF x g => by
    change c • F.1 _ = c • F.1 _
    rw [hF]

def vanM (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) : Submodule ℂ (Sm E (r + s)) where
  carrier := {F | ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0}
  add_mem' := fun {F G} hF hG m => by
    change F.1 _ + G.1 _ = 0
    rw [hF, hG, add_zero]
  zero_mem' := fun _ => rfl
  smul_mem' := fun c F hF m => by
    change c • F.1 _ = 0
    rw [hF, smul_zero]

theorem aeval_mem_Zalg {n : ℕ} {x : Module.End ℂ (Sm E n)} (hx : x ∈ Zalg E n) (q : Polynomial ℂ) :
    Polynomial.aeval x q ∈ Zalg E n := by
  rw [← Polynomial.aeval_subalgebra_coe q (Zalg E n) ⟨x, hx⟩]
  exact (Polynomial.aeval (⟨x, hx⟩ : Zalg E n) q).2

theorem cap_mem_Zalg {n : ℕ} (τ : E →+* ℂ) (u : ℂ) : cap (a := n) τ u ∈ Zalg E n :=
  Algebra.subset_adjoin ⟨τ, u, rfl⟩

theorem centre (J : Set (Module.End ℂ (Sm E (r + s)))) (hJ : Cofin J) :
    ∃ (J₁ : Set (Module.End ℂ (Sm E r))) (J₂ : Set (Module.End ℂ (Sm E s))), Cofin J₁ ∧ Cofin J₂ ∧
    (∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → (∀ z ∈ J, z F = 0) →
      ∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ z ∈ J₁, z G = 0) ∧
    (∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → (∀ z ∈ J, z F = 0) →
      ∀ G : Sm E s, (∀ m, G.1 m = F.1 (lev (Ad E) r s (1, m))) → ∀ z ∈ J₂, z G = 0) := by
  let W₀ : Set (Sm E (r + s)) := {F | F ∈ leftN E r s ∧ ∀ z ∈ J, z F = 0}
  have key : ∀ τ : E →+* ℂ, (∀ u, ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀, Polynomial.aeval (capR r s τ u) q F ∈ vanM E r s) ∧
      ∀ u, ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀, Polynomial.aeval (capS r s τ u) q F ∈ vanM E r s := by
    intro τ
    obtain ⟨a, a1, a2, a3⟩ := _root_.GlobalTheory.CompanionTheory.CTFin.QdetCoeff.qdet_shift_coeff (Module.End ℂ (Sm E (r + s))) r
      (fun i j : Fin r => Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s j)) (((r : ℂ) - 1) / 2)
    obtain ⟨b, b1, b2, b3⟩ := _root_.GlobalTheory.CompanionTheory.CTFin.QdetCoeff.qdet_shift_coeff (Module.End ℂ (Sm E (r + s))) s
      (fun i j : Fin s => Eop (a := r + s) τ (Fin.natAdd r i) (Fin.natAdd r j)) (((s : ℂ) - 1) / 2)
    refine _root_.GlobalTheory.CompanionTheory.Dblock.CentreBlocks.monic_relations_to_blocks (Sm E (r + s)) (fun u => cap (a := r + s) τ u) (capR r s τ) (capS r s τ) (leftN E r s) (vanM E r s) W₀
      (-(s : ℂ) / 2) ((r : ℂ) / 2) r s a b (fun u v => (_root_.GlobalTheory.CompanionTheory.CTFin.CapComm.capR_capS_commute E r s τ u v).1)
      (fun u v => (_root_.GlobalTheory.CompanionTheory.CTFin.CapComm.capR_capS_commute E r s τ u v).2.1) (fun u v => (_root_.GlobalTheory.CompanionTheory.CTFin.CapComm.capR_capS_commute E r s τ u v).2.2)
      (fun u F hF => (GlobalTheory.T.capelli_constant_term_vanishing E r s τ u F).2 hF) (fun u F hF => ((GlobalTheory.T.capelli_constant_term_vanishing E r s τ u F).1 hF).1)
      (fun u F hF => ((GlobalTheory.T.capelli_constant_term_vanishing E r s τ u F).1 hF).2) ?_ a1 a2 a3 b1 b2 b3 (fun F hF => hF.1) ?_
    · intro u F hF m
      have := GlobalTheory.T.capelli_levi_factorization_sum E r s τ u F hF m
      change (cap (a := r + s) τ u F).1 _ - (capS r s τ (u + (r : ℂ) / 2) (capR r s τ (u + -(s : ℂ) / 2) F)).1 _ = 0
      rw [this, sub_eq_zero]
      have e : u + -(s : ℂ) / 2 = u - (s : ℂ) / 2 := by ring
      rw [e]
    · intro u
      obtain ⟨p, hp, h⟩ := _root_.GlobalTheory.CompanionTheory.CTFin.cofin_monic_on_killed E (r + s) J hJ _ (cap_mem_Zalg τ u)
      exact ⟨p, hp, fun F hF => h F hF.2⟩
  choose q₁ m₁ h₁ using fun τ => (key τ).1
  choose q₂ m₂ h₂ using fun τ => (key τ).2
  refine ⟨{z | ∃ (τ : E →+* ℂ) (u : ℂ), z = Polynomial.aeval (cap (a := r) τ u) (q₁ τ u)},
    {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = Polynomial.aeval (cap (a := s) τ u) (q₂ τ u)}, ?_, ?_, ?_, ?_⟩
  · refine GlobalTheory.T.cofinite_of_capelli_monic E r _ ?_ fun τ u => ⟨q₁ τ u, m₁ τ u, τ, u, rfl⟩
    rintro _ ⟨τ, u, rfl⟩
    exact aeval_mem_Zalg (cap_mem_Zalg τ u) _
  · refine GlobalTheory.T.cofinite_of_capelli_monic E s _ ?_ fun τ u => ⟨q₂ τ u, m₂ τ u, τ, u, rfl⟩
    rintro _ ⟨τ, u, rfl⟩
    exact aeval_mem_Zalg (cap_mem_Zalg τ u) _
  · rintro F hF hz G hG _ ⟨τ, u, rfl⟩
    refine Subtype.ext (funext fun m => ?_)
    rw [(GlobalTheory.T.capelli_restrict_levi E r s τ u (q₁ τ u) F).1 G hG m]
    exact h₁ τ u F ⟨hF, hz⟩ (m, 1)
  · rintro F hF hz G hG _ ⟨τ, u, rfl⟩
    refine Subtype.ext (funext fun m => ?_)
    rw [(GlobalTheory.T.capelli_restrict_levi E r s τ u (q₂ τ u) F).2 G hG m]
    exact h₂ τ u F ⟨hF, hz⟩ (1, m)

theorem exists_mem_goodCT (L : Subgroup (GL (Fin (r + s)) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E (r + s)) W) (J : Set (Module.End ℂ (Sm E (r + s))))
    (hJ : Cofin J) (φ : Sm E (r + s)) (hφ : φ ∈ genSpace L ρ J)
    [MeasurableSpace (BlockIx (r + s) r → Ad E)] [BorelSpace (BlockIx (r + s) r → Ad E)]
    (μ : Measure (BlockIx (r + s) r → Ad E)) (𝓕 : Set (BlockIx (r + s) r → Ad E)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratN E (r + s) r) 𝓕 μ) :
    ∃ F ∈ goodCT L ρ J, ∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ := by
  obtain ⟨hA, hLf, hK, hZ⟩ := hφ
  obtain ⟨F, hF1, hF2⟩ := _root_.GlobalTheory.CompanionTheory.CTSmooth.ct_smooth E (r + s) r φ hA.left hA.level μ 𝓕 hμ h𝓕
  have hlie : ∀ φ' F' : Sm E (r + s), (∀ (γ : GL (Fin (r + s)) E) (g : GA E (r + s)), φ'.1 (ratGL E (r + s) γ * g) = φ'.1 g) →
      IsOpen {k | finRep E (r + s) k φ' = φ'} → (∀ g, F'.1 g = ∫ x in 𝓕, φ'.1 (unip x * g) ∂μ) →
      ∀ (X : Lie E (r + s)) (g : GA E (r + s)), (lie E (r + s) X F').1 g = ∫ x in 𝓕, (lie E (r + s) X φ').1 (unip x * g) ∂μ := by
    intro φ' F' h1 h2 h3 X g
    obtain ⟨F'', e1, e2⟩ := _root_.GlobalTheory.CompanionTheory.CTSmooth.ct_smooth E (r + s) r φ' h1 h2 μ 𝓕 hμ h𝓕
    have : F' = F'' := Subtype.ext (funext fun g => (h3 g).trans (e1 g).symm)
    rw [this]
    exact e2 X g
  refine ⟨F, ⟨fun x g => ?_, fun γ g => ?_, fun k hk => ?_, fun g => ?_, fun g => ?_, fun z hz => ?_⟩, hF1⟩
  · rw [hF1, hF1]
    exact _root_.GlobalTheory.CompanionTheory.CTFin.constTerm_unip_left E (r + s) r φ hA.left hA.level μ 𝓕 hμ h𝓕 x g
  · rw [hF1, hF1]
    exact _root_.GlobalTheory.CompanionTheory.CTFin.integral_unip_lev_mul E r s φ hA.left hA.level μ 𝓕 hμ h𝓕 γ g
  · refine Subtype.ext (funext fun g => ?_)
    change F.1 (g * finGL E (r + s) k) = F.1 g
    rw [hF1, hF1]
    refine congrArg (fun f : (BlockIx (r + s) r → Ad E) → ℂ => ∫ x in 𝓕, f x ∂μ) (funext fun x => ?_)
    have := congrFun (congrArg Subtype.val (hLf k hk)) (unip x * g)
    rw [← this]
    change _ = φ.1 (unip x * g * finGL E (r + s) k)
    rw [mul_assoc]
  · have h := _root_.GlobalTheory.CompanionTheory.CTFin.KType.ct_mem_coeffSpan E (r + s) r φ hA.left hA.level W ρ hK μ 𝓕 hμ h𝓕 g
    convert h using 1
    funext k
    exact hF1 _
  · obtain ⟨C, N, h⟩ := _root_.GlobalTheory.CompanionTheory.CTFin.Growth.ct_growth E (r + s) r φ hA μ 𝓕 hμ h𝓕 g
    exact ⟨C, N, fun y => by rw [hF1]; exact h y⟩
  · refine Subtype.ext (funext fun g => ?_)
    rw [_root_.GlobalTheory.CompanionTheory.CTFin.Central.ct_Zalg E (r + s) r μ 𝓕 hμ h𝓕 hlie φ F hA.left hA.level hF1 z (hJ.1 hz) g, hZ z hz]
    simp

theorem finiteDimensional_goodCT (h₁ : GenFin E r) (h₂ : GenFin E s) (L : Subgroup (GL (Fin (r + s)) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin (r + s)) (Af E)))) {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (Kinf E (r + s)) W) (hρ : GlobalTheory.Published.AutFin.IsContRep ρ)
    (J : Set (Module.End ℂ (Sm E (r + s)))) (hJ : Cofin J) : FiniteDimensional ℂ (goodCT L ρ J) := by
  obtain ⟨J₁, J₂, c₁, c₂, k₁, k₂⟩ := centre J hJ
  obtain ⟨T, hT⟩ := _root_.GlobalTheory.CompanionTheory.CTFin.IwaAd.iwasawa_finite_cosets E r s L hL
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.CompanionTheory.CTFin.UniSol.coeffSpan_unisolvent (Kinf E (r + s)) W ρ
  have key : ∀ (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)),
      ∃ 𝓥 : Submodule ℂ (GA E r × GA E s → ℂ), FiniteDimensional ℂ 𝓥 ∧ ∀ F ∈ goodCT L ρ J,
        (fun m => F.1 (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ))) ∈ 𝓥 := by
    intro t κ
    obtain ⟨L₁, ρ₁, o₁, q₁, e₁⟩ := _root_.GlobalTheory.CompanionTheory.CTFin.Slice1.slice_mem_genSpace E r s L hL W ρ hρ J hJ J₁ c₁ k₁ t κ
    obtain ⟨L₂, ρ₂, o₂, q₂, e₂⟩ := GlobalTheory.T.constant_term_unseen_statement_b E r s L hL W ρ hρ J hJ J₂ c₂ k₂ t κ
    have f₁ := h₁ L₁ o₁ W ρ₁ q₁ J₁ c₁
    have f₂ := h₂ L₂ o₂ W ρ₂ q₂ J₂ c₂
    obtain ⟨𝓥, fd, hV⟩ := _root_.GlobalTheory.CompanionTheory.CTFin.ProdTrick.exists_finiteDimensional_of_slices (GA E r) (GA E s)
      ((Submodule.span ℂ (genSpace L₁ ρ₁ J₁)).map (Sm E r).subtype)
      ((Submodule.span ℂ (genSpace L₂ ρ₂ J₂)).map (Sm E s).subtype) inferInstance inferInstance
    refine ⟨𝓥, fd, fun F hF => hV _ (fun m₂ => ?_) (fun m₁ => ?_)⟩
    · obtain ⟨G, hG, e⟩ := e₁ F hF m₂
      exact ⟨G, Submodule.subset_span hG, funext e⟩
    · obtain ⟨G, hG, e⟩ := e₂ F hF m₁
      exact ⟨G, Submodule.subset_span hG, funext e⟩
  choose 𝓥 fd hV using key
  let Ψ : goodCT L ρ J →ₗ[ℂ] ∀ p : T × S, 𝓥 p.1.1 p.2.1 :=
    { toFun := fun F p => ⟨_, hV p.1.1 p.2.1 F.1 F.2⟩
      map_add' := fun F G => rfl
      map_smul' := fun c F => rfl }
  have hΨ : Function.Injective Ψ := by
    refine (injective_iff_map_eq_zero Ψ).2 fun F hF => ?_
    obtain ⟨F, a1, a2, a3, a4, a5, a6⟩ := F
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    obtain ⟨x, m, t, k, l, ht, hl, rfl⟩ := hT g
    have e0 : ∀ κ ∈ S, F.1 (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) = 0 := by
      intro κ hκ
      have := congrFun (congrArg Subtype.val (congrFun hF (⟨t, ht⟩, ⟨κ, hκ⟩))) m
      exact this
    have hc := hS _ (a4 (lev (Ad E) r s m * finGL E (r + s) t)) e0
    have h1 := congrFun hc k
    have h2 := congrFun (congrArg Subtype.val (a3 l hl))
      (unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k))
    change F.1 (_ * finGL E (r + s) l) = _ at h2
    refine h2.trans ?_
    have e1 : unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) =
        unip x * (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k)) := by
      simp only [mul_assoc]
    rw [e1, a1]
    exact h1
  exact FiniteDimensional.of_injective Ψ hΨ

theorem ctFin : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ b < a, GenFin E b) →
    ∀ r, 0 < r → r < a → CTFin E a r := by
  intro E _ _ _ a hG r h0 hr
  obtain ⟨s, rfl⟩ : ∃ s, a = r + s := ⟨a - r, by omega⟩
  intro L hL W _ _ _ ρ hρ J hJ
  have hfd := finiteDimensional_goodCT (hG r hr) (hG s (by omega)) L hL ρ hρ J hJ
  refine ⟨(goodCT L ρ J).map (Sm E (r + s)).subtype, inferInstance, ?_⟩
  intro φ hφ _ _ μ 𝓕 hμ h𝓕
  obtain ⟨F, hF, e⟩ := exists_mem_goodCT L ρ J hJ φ hφ μ 𝓕 hμ h𝓕
  exact ⟨F, hF, funext e⟩

end GlobalTheory.CompanionTheory.CTFin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnTau
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Cell
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CellTop

open GlobalTheory.CompanionTheory.MuC

variable {D : D7} {p : ℕ}

theorem mem_cell_iff {e : AE D} (hee : e * e = e) (g : G D p) : g ∈ cell e ↔ InCell e g :=
  isUnit_mix_iff hee (cB g)

theorem continuous_cB : Continuous (cB : G D p → Mx D p p) := by
  have hm : Continuous (mat : G D p → Mx D (p + p) (p + p)) := Units.continuous_val.comp continuous_subtype_val
  exact continuous_matrix fun i j => hm.matrix_elem _ _

theorem continuous_dB : Continuous (dB : G D p → Mx D p p) := by
  have hm : Continuous (mat : G D p → Mx D (p + p) (p + p)) := Units.continuous_val.comp continuous_subtype_val
  exact continuous_matrix fun i j => hm.matrix_elem _ _

theorem cell_eq {e : AE D} (hee : e * e = e) :
    cell e = (fun g : G D p => (cB g).det) ⁻¹' {z : AE D | IsUnit (1 - e + e * z)} := by
  ext g
  change IsUnit _ ↔ IsUnit _
  rw [det_mix_one hee]


open Classical in
def tau (e : AE D) (g : G D p) : hermS D p e := if h : ∃ x, IsB e g x then h.choose else 0

theorem isB_tau {e : AE D} {g : G D p} (h : ∃ x, IsB e g x) : IsB e g (tau e g) := by
  rw [tau, dite_eq_left h]
  exact h.choose_spec

theorem tau_eq {e : AE D} {g : G D p} {x : hermS D p e} (h : IsB e g x) : tau e g = x :=
  isB_unique (isB_tau ⟨x, h⟩) h

theorem tau_formula {e : AE D} (hee : e * e = e) {g : G D p} {x : hermS D p e} (hu : g ∈ cell e) (h : IsB e g x) :
    Ring.inverse (1 - e + e * (cB g).det) • (((1 - e) • (1 : Mx D p p) + e • cB g).adjugate * (e • dB g)) = x.1.1 := by
  have hu' : IsUnit (1 - e + e * (cB g).det) := by
    have := hu
    rw [cell_eq hee] at this
    exact this
  exact mix_solve hee hu' x.2 h.2

theorem continuousOn_tau {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) (hee : e * e = e) (hce : cA D e = e) :
    ContinuousOn (tau e : G D p → hermS D p e) (cell e) := by
  have : IsTopologicalRing (AE D) := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hd : Continuous fun g : G D p => (cB g).det := continuous_cB.matrix_det
  have h1 : ContinuousOn (fun g : G D p => Ring.inverse (1 - e + e * (cB g).det)) (cell e) := by
    refine (unit_AE he).2.comp hd.continuousOn ?_
    intro g hg
    rw [cell_eq hee] at hg
    exact hg
  have h2 : Continuous fun g : G D p => ((1 - e) • (1 : Mx D p p) + e • cB g).adjugate * (e • dB g) := by
    refine Continuous.matrix_mul (Continuous.matrix_adjugate ?_) (continuous_dB.const_smul e)
    exact continuous_const.add (continuous_cB.const_smul e)
  have h3 : ContinuousOn (fun g : G D p => ((tau e g).1.1 : Mx D p p)) (cell e) := by
    refine (h1.smul h2.continuousOn).congr fun g hg => ?_
    have hB : IsB e g (tau e g) := isB_tau (exists_isB hee hce ((mem_cell_iff hee g).1 hg))
    exact (tau_formula hee hg hB).symm
  have i1 : Topology.IsInducing (Subtype.val : hermS D p e → hermA D p) := Topology.IsInducing.subtypeVal
  have i2 : Topology.IsInducing (Subtype.val : hermA D p → Mx D p p) := Topology.IsInducing.subtypeVal
  exact (i2.comp i1).continuousOn_iff.2 h3

theorem cellAlg : IdemEx → CellAlg := by
  intro hI D p nb hnb w hw S e he
  obtain ⟨hee, hce⟩ := (hI D S).2 e he
  have hex : ∀ g ∈ cell (p := p) e, IsB e g (tau e g) := fun g hg =>
    isB_tau (exists_isB hee hce ((mem_cell_iff hee g).1 hg))
  have hcell : ∀ {g : G D p} {x : hermS D p e}, IsB e g x → g ∈ cell e := fun h => (mem_cell_iff hee _).2 h.1
  refine ⟨tau e, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, continuousOn_tau he hee hce, (continuous_nb hnb).comp continuous_subtype_val,
      fun x y => isNMap_add hnb x.1 y.1⟩
    · rw [cell_eq hee]
      exact (unit_AE he).1.preimage (continuous_cB.matrix_det (R := AE D))
    · intro q hq x hx
      have h := (LeftCell.isB_left hq (tau e x)).2 (hex x hx)
      exact ⟨hcell h, (tau_eq h)⟩
    · intro y x hx
      have h := (isB_mul_nb hnb y (tau e x)).2 (hex x hx)
      exact ⟨hcell h, tau_eq h⟩
  · intro g hg u hu
    exact hcell ((isB_mul_right_iff he hu (tau e g)).2 (hex g hg))
  · intro g hg
    have h := hex g hg
    change (e • cB g) * _ = _
    rw [smul_mul_assoc]
    have h2 : cB g * (tau e g).1.1 = e • dB g := h.2
    rw [h2, smul_smul, hee]

end GlobalTheory.CompanionTheory.CellTop
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSwapProductGenericStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_swap_product_generic : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.CuspGeneric k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)), (∀ a, (x a).IsCusp) → ∀ (hd : ∑ a, (x a).1 = N) (j : ℕ) (hj : j + 1 < h) (hd' : ∑ a, (x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsGenericFor ψ σ → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)) hd') := by
  first | exact @GlobalTheory.CompanionTheory.GenSwap.isSubquotient_prodIrr_swap | exact GlobalTheory.CompanionTheory.GenSwap.isSubquotient_prodIrr_swap | (intros; apply GlobalTheory.CompanionTheory.GenSwap.isSubquotient_prodIrr_swap <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCovariance
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar

theorem covar_of (hB : Bruhat) (hR : RatPts) : Covar := by
  intro D n V ψ χ θ μ ω hS γ hγ v Φ Ψ hΨ
  obtain ⟨-, -, -, -, -, -, ⟨𝓕, hC⟩, hW⟩ := hS
  have hF : FieldGen D.host.E (D.sp.cm.sig : D.host.E →+* D.host.E) n :=
    FieldGenPf.fieldGen_of_bruhat hB D.host.E _ (fun x => star_star x) two_ne_zero n
  exact Transfer.ratPts_transfer hR D n hF (CovAt ψ V ω) (fun _ _ h₁ h₂ => covAt_mul h₁ h₂)
    (fun g a h => covAt_levi D n V ψ χ θ μ ω hW g a h)
    (fun g b hb h => covAt_unip D n V ψ χ θ μ ω hW g b hb h)
    (fun g h => covAt_weyl D n V ψ χ θ μ ω hW hC.1 g h) γ hγ v Φ Ψ hΨ

theorem covar : Covar :=
  covar_of GlobalTheory.CompanionTheory.BruhatCell.bruhat GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn

end GlobalTheory.CompanionTheory.EisCovar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiCoefficientOfBoundStatement
section
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_jacobi_coefficient_of_bound : PcBound → CfFJ := by
  first | exact @GlobalTheory.CompanionTheory.CfFJ.cfFJ_of_pcBound | exact GlobalTheory.CompanionTheory.CfFJ.cfFJ_of_pcBound | (intros; apply GlobalTheory.CompanionTheory.CfFJ.cfFJ_of_pcBound <;> assumption)
end

