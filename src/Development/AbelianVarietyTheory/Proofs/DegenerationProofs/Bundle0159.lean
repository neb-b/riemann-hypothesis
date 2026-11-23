module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoOnG
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericIsoOfUniformisationsIsoData
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAbelianSchemeOfAbelianThickenings
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0158

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartsIsoLabelsOfThetaPointAndValues
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.Ex.AbPartIso
section
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N N' : NumD F} (ν : NumOf D F N) (ν' : NumOf D' F N') {φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A}

theorem Carries.eq {ν : NumOf D F N} {ν' : NumOf D' F N'} {x : N.A} {x' : N'.A} (h : Carries ν ν' φ x x') :
    lift (𝟙 _) (ν.eA x) ≫ φ.hom ≫ snd _ _ = ν'.eA x' := by
  rw [← Category.assoc, h, lift_snd]

theorem exists_equiv (hφ : HomF φ) : ∃ f : N.A ≃* N'.A, ∀ x, Carries ν ν' φ x (f x) := by
  have hi : φ.inv ≫ fst _ _ = fst _ _ := by rw [Iso.inv_comp_eq, hφ.1]
  have c : ∀ x, Carries ν ν' φ x (ν'.eA.symm (lift (𝟙 _) (ν.eA x) ≫ φ.hom ≫ snd _ _)) := fun x => by
    unfold Carries
    ext1
    · rw [Category.assoc, hφ.1, lift_fst, lift_fst]
    · rw [lift_snd, MulEquiv.apply_symm_apply, Category.assoc]
  let f : N.A →* N'.A := MonoidHom.mk' (fun x => ν'.eA.symm (lift (𝟙 _) (ν.eA x) ≫ φ.hom ≫ snd _ _)) fun x y => by
    rw [map_mul ν.eA, hφ.2, map_mul]
  refine ⟨MulEquiv.ofBijective f ⟨fun x y h => ?_, fun y => ?_⟩, c⟩
  · have e : lift (𝟙 _) (ν.eA x) ≫ φ.hom = lift (𝟙 _) (ν.eA y) ≫ φ.hom :=
      (c x).trans ((congrArg (fun z => lift (𝟙 _) (ν'.eA z)) h).trans (c y).symm)
    have := congrArg (· ≫ snd _ _) ((cancel_mono _).1 e)
    simp only [lift_snd] at this
    exact ν.eA.injective this
  · refine ⟨ν.eA.symm (lift (𝟙 _) (ν'.eA y) ≫ φ.inv ≫ snd _ _), ν'.eA.symm_apply_eq.2 ?_⟩
    have e : lift (𝟙 _) (lift (𝟙 _) (ν'.eA y) ≫ φ.inv ≫ snd _ _) = lift (𝟙 _) (ν'.eA y) ≫ φ.inv := by
      ext1
      · rw [Category.assoc, hi, lift_fst, lift_fst]
      · rw [lift_snd, Category.assoc]
    rw [MulEquiv.apply_symm_apply, e, Category.assoc, Iso.inv_hom_id_assoc, lift_snd]

theorem wVal_ne (w : BunIso φ) {f : N.A → N'.A} {x : N.A} (h : Carries ν ν' φ x (f x)) : wVal ν ν' w f x ≠ 0 := by
  have z : Sp F := (default : PrimeSpectrum F)
  have e₁ : (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left = (ν.eA x).left := by
    rw [← Over.comp_left, lift_snd]
  have e₂ : (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left =
      (ν'.eA (f x)).left := by
    rw [← Over.comp_left, h.eq]
  have m₁ : ((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left) z ∈
      D.P.L.U (ν.J (ν.eA x).left) := by rw [e₁]; exact ν.good _ trivial
  have m₂ : ((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left) z ∈
      D'.P.L.U (ν'.J (ν'.eA (f x)).left) := by rw [e₂]; exact ν'.good _ trivial
  have hle : ⊤ ≤ (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ⁻¹ᵁ
      (LB.div (D'.P.L.pull (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left)
        (D.P.L.pull (snd (TF (R := R) F) D.P.A).left)).U
        (fun _ => ν'.J (ν'.eA (f x)).left, fun _ => ν.J (ν.eA x).left) := by
    intro y _
    have : y = z := by
      letI := y.isPrime
      letI := z.isPrime
      exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime _).symm)
    subst y
    exact ⟨mem_pull.2 m₂, mem_pull.2 m₁⟩
  unfold wVal valF
  rw [dite_eq_left hle]
  exact ((w.s _).isUnit.map _ |>.map _).ne_zero

theorem exists_iso (hG : GlobalFnsSt) (w : BunIso φ) (hφ : HomF φ) (hw : w.IsGen) (hne : ∃ x, N'.th x ≠ 0) :
    ∃ I : NumB.Iso N.toNumB N'.toNumB, GeoIso ν ν' I ∧ ∀ x, Carries ν ν' φ x (I.φ x) := by
  obtain ⟨f, hf⟩ := exists_equiv ν ν' hφ
  have h₁ := _root_.GlobalTheory.Ex.AbPartCube.theta_move hG R D D' F N N' ν ν' φ w f hφ hw hf
  have h₂ := GlobalTheory.T.abelianPartIso_carries_symmetry_values hG R D D' F N N' ν ν' φ w f hφ hw hf
  obtain ⟨c, h₃⟩ := _root_.GlobalTheory.Ex.AbPartIso.exists_th_scale R D D' F N N' ν ν' φ w f hφ hw hf
  have h₀ := fun x => wVal_ne ν ν' w (hf x)
  have hc : c ≠ 0 := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨y, rfl⟩ := f.surjective x
    rintro rfl
    exact hx (by rw [h₃, zero_mul, zero_mul])
  have h1 := h₀ 1
  refine ⟨⟨f, fun x => Units.mk0 (wVal ν ν' w f x / wVal ν ν' w f 1) (div_ne_zero (h₀ x) h1), Units.ext (div_self h1),
    fun x y u => Units.ext ?_, fun x => Units.ext ?_, Units.mk0 (c * wVal ν ν' w f 1) (mul_ne_zero hc h1), fun x => ?_⟩,
    ⟨φ, w, wVal ν ν' w f, hφ.1, hw, hf, fun _ => rfl, fun x => div_mul_cancel₀ _ h1⟩, hf⟩
  · simp only [Units.val_mul, Units.val_mk0]
    field_simp
    linear_combination h₁ x y u
  · simp only [Units.val_mul, Units.val_mk0]
    field_simp
    linear_combination h₂ x
  · simp only [Units.val_mul, Units.val_mk0]
    rw [h₃]
    field_simp
end

theorem main : Laws → ThetaPtDeterminesSt → BrUthSt → UrCSt := by
  intro hL hQ hU R _ _ D D' e₁ b₁ e₂ b₂ C _ _ _ _ _ N N' ν ν' q q' n hn ho hnC hI hI' hT hT' mt hA hg e hB hTm
  have hn0 : (n : C) ≠ 0 := fun h => by rw [h, norm_zero] at hnC; exact zero_ne_one hnC
  obtain ⟨Q, Φ, hΦ⟩ := exists_isFib hL.polBaseChange D C
  obtain ⟨Q', Φ', hΦ'⟩ := exists_isFib hL.polBaseChange D' C
  obtain ⟨j₀, H⟩ := _root_.GlobalTheory.Ex.FibIso.exists_iso_fib hL hQ hU R D D' e₁ b₁ e₂ b₂ hg C N N' ν ν' Q Q' Φ Φ' hΦ hΦ' n hn ho hn0
  choose ρ hρ hρ' hρ'' using _root_.GlobalTheory.Ex.TorsMatch.exists_torsMap C N N' q q' n _ _ hn ho hnC hI hI' hT hT' mt hA e hTm
  have key : ∀ j, j₀ ≤ j → ∃ I : NumB.Iso N.toNumB N'.toNumB, GeoIso ν ν' I ∧
      ∀ b, b ^ (n ^ j) ^ 2 = 1 → I.φ b = ρ j b := fun j hj => by
    obtain ⟨σ, hσ, hs⟩ := H j hj _ _ mt.c₀_ne (hρ j)
    obtain ⟨φ, w, hφ, hw, hp⟩ := GlobalTheory.T.exists_product_iso_of_fibre_iso_field R D D' C Q Q' Φ Φ' hΦ hΦ' σ hσ
    obtain ⟨t, -, ht⟩ := hT'.good 1
    obtain ⟨I, hI, hc⟩ := exists_iso ν ν' hL.globalFns w hφ hw ⟨_, fun h => by
      rw [h, norm_zero] at ht; exact zero_ne_one ht⟩
    refine ⟨I, hI, fun b hb => ν'.eA.injective ?_⟩
    exact (hc b).eq.symm.trans (Carries.eq (hp _ _ fun x hx => hs x b hb hx))
  obtain ⟨I, hG, hI₀⟩ := key (j₀ + 1) (Nat.le_succ _)
  have om : ∀ j, Odd (n ^ j) := fun j => ho.pow
  refine ⟨I, fun i p p' hr h1 h1' => ?_, ?_, hG⟩
  · obtain ⟨I', -, hI₁⟩ := key (j₀ + 1 + i) (by omega)
    have ag : ∀ b, b ^ (n ^ (j₀ + 1)) ^ 2 = 1 → I'.φ b = I.φ b := fun b hb => by
      obtain ⟨p, p', hr, a, a', rfl⟩ := hρ'' _ b hb
      rw [hI₀ _ hb, ← hρ' _ _ le_rfl p p' hr a a', hI₁, ← hρ' _ _ (by omega) p p' hr a a']
      rw [pow_add, mul_pow, pow_mul, hb, one_pow]
    have eq : ∀ x, I'.φ x = I.φ x := fun x => by
      refine hT'.sep (j₀ + 1) (by omega) _ _
        ((I'.lam * I'.h x ^ (n ^ (j₀ + 1)) ^ 2 / (I.lam * I.h x ^ (n ^ (j₀ + 1)) ^ 2) : Cˣ) : C) (Units.ne_zero _)
        fun b' hb' => ?_
      obtain ⟨b, rfl⟩ := I.φ.surjective b'
      have hb : b ^ (n ^ (j₀ + 1)) ^ 2 = 1 := I.φ.injective (by rw [map_pow, hb', map_one])
      rw [RecPeriods.uth_iso I _ (om _) b x hb, ← ag b hb, RecPeriods.uth_iso I' _ (om _) b x hb, ← _root_.mul_assoc,
        ← Units.val_mul, div_mul_cancel]
    have hb : p.1.2.b ^ n ^ i = 1 := by rw [N.QT_pow_b, h1, toAdd_one, N.c_zero]
    rw [← eq, hI₁, hρ' (j₀ + 1 + i) i (by omega) p p' hr h1 h1']
    rw [← pow_mul, show (j₀ + 1 + i) * 2 = i + (2 * j₀ + 2 + i) by ring, pow_add, pow_mul, hb, one_pow]
  · obtain ⟨t, ht, ht'⟩ := hT.good 1
    have dv : ∀ (j : ℕ) (x : N.A), ∃ y, y ^ n ^ j = x := fun j => by
      induction j with
      | zero => exact fun x => ⟨x, by rw [pow_zero, pow_one]⟩
      | succ j ih =>
        intro x
        obtain ⟨y, rfl⟩ := hT.div x
        obtain ⟨z, rfl⟩ := ih y
        exact ⟨z, by rw [pow_succ, pow_mul]⟩
    obtain ⟨b, rfl⟩ := dv (j₀ + 1) t
    have hb : b ^ (n ^ (j₀ + 1)) ^ 2 = 1 := by
      rw [sq, pow_mul, pow_succ' n j₀, pow_mul _ n, ← pow_succ', ht, one_pow]
    have a := RecPeriods.uth_iso I _ (om _) b 1 hb
    rw [map_one, hI₀ b hb, ((hρ _).2 b hb).2, I.h_one, one_pow, _root_.mul_one] at a
    have nz : N.uth (n ^ (j₀ + 1)) b 1 ≠ 0 := by
      refine mul_ne_zero (Units.ne_zero _) (mul_ne_zero (fun h => ?_) (Units.ne_zero _))
      rw [_root_.one_mul] at ht' h
      rw [h, norm_zero] at ht'
      exact zero_ne_one ht'
    exact (mul_right_cancel₀ nz a).symm

end GlobalTheory.Ex.AbPartIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcTorsionLabelsActionCompatStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcTorsionLabels_action_compat : Laws → BrGtSt → AllD fun {E} _ _ _ {H} D => letI := H.starRing; ∀ (R : Type) [CommRing R] [IsDomain R] (C : Type) [NormedField C] [IsAlgClosed C] [Algebra (FractionRing R) C] (A : ArcF D R C) (o : Full D C) (M : Mdl o), M.P.TorsionIso → ∀ (N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (k : ℕ) (β : A.N.Form k) (u r : Cˣ) (J : NumD.Iso (A.N.twist β u) N') (j : ℕ), 0 < j → r ^ j = u → (∀ x (p : (A.N.twist β u).QT j) (q' : N'.QT j) p' z, TwRel β u r (A.q _ x) p → q'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 q'.1.2 → ν'.QPt p' q' → z.left = (o.I.ev j x).left ≫ M.φ → M.P.ToA C j p' z) → ∀ (x : 𝓞 E) (b : A.N.A), b ^ j = 1 → J.φ (actV (N := A.N) A.ν A.oa.onB x b) = actV ν' M.P.oD.onB x (J.φ b) := by
  first | exact @GlobalTheory.Relabel.act_compat_on_torsion | exact GlobalTheory.Relabel.act_compat_on_torsion | (intros; apply GlobalTheory.Relabel.act_compat_on_torsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionAbelianVarietyLeConstMulPow
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem card_torsion_le : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), AmpleCub B L → ∀ a, SmoothOfRelativeDimension a B.hom → ∃ C : ℕ, ∀ n : ℕ, (n : k) ≠ 0 → Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ∧ Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ≤ C * n ^ (2 * a) := by
  intro k _ _ B _ hB L _ a ha
  refine ⟨1, fun n hn => ?_⟩
  have h := _root_.GlobalTheory.abMulN_holds k B a n hB ha hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn Nat.cast_zero
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [h]
    exact pow_ne_zero _ hn0
  · rw [h, Nat.one_mul]

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericIsoOfUniformisationsIsoDataStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generic_iso_of_uniformisations_isoData : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D D' : DegData R I) (A A' : PolAV (Sp (FractionRing R))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre), ∃ ψ : A'.A ≅ A.A, IsMonHom ψ.hom ∧ LBIso A'.L (A.L.pull ψ.hom.left) ∧ (∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (p' : QkPt D'.toPre F k) (x' : TFK (R := R) F ⟶ A'.A), p'.y = hD.xe.symm p.y → IsPullGtF (RingHom.id R) hD F p.g p'.g → (QkToAkU U'.toUnifPre F k p' x' ↔ QkToAkU U.toUnifPre F k p (x' ≫ ψ.hom))) ∧ ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (o : D.OAct O) (o' : D'.OAct O) (oA : A.OAct O) (oA' : A'.OAct O) (oG : RingAct G O) (oG' : RingAct G' O), U.OLinear O o oA oG → U'.OLinear O o' oA' oG' → (∀ (x : O) y, hD.xe (x • y) = x • hD.xe y) → (∀ x, o'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (o.onB.act x)) → ∀ x, oA'.act x ≫ ψ.hom = ψ.hom ≫ oA.act x := by
  first | exact @GlobalTheory.exists_generic_iso_of_unif | exact GlobalTheory.exists_generic_iso_of_unif | (intros; apply GlobalTheory.exists_generic_iso_of_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionsBasisBaseChangeH1Vanishing
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecBasis

theorem exists_sec_of_ker {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)}
    {M : LB Y} (P : Perf f M) (v : Fin P.a → R) (hv : P.D₀.mulVec v = 0) :
    ∃ s : LB.Sec M, ∀ i, rs Y (P.le i) (s.f (P.ch i)) = Seesaw.loc₀ P v i := by
  have h : IsPullback (𝟙 Y) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E, hE⟩ := P.sec R (RingHom.id R) Y (𝟙 Y) f h
  let t := E ⟨v, hv⟩
  have le : ∀ j, M.U j ≤ (M.pull (𝟙 Y)).U (fun _ => j) := fun j => le_pull M (𝟙 Y) le_rfl
  refine ⟨⟨fun j => rs Y (le j) (t.f fun _ => j), fun i j => ?_⟩, fun i => ?_⟩
  · have e := GlobalTheory.LB.sec_rel t (fun _ => i) (fun _ => j) (inf_le_left.trans (le i))
      (inf_le_right.trans (le j)) (inf_le_inf (le i) (le j))
    have e' := (GlobalTheory.LB.resG_pull_g (L := M) (𝟙 Y) (fun _ => i) (fun _ => j)
      (inf_le_inf (le i) (le j))).trans (rs_self _ _)
    exact (rs_rs _ _ _).trans (e.trans (congrArg₂ (· * ·) e' (rs_rs _ _ _).symm))
  · exact (rs_rs _ _ _).trans (hE ⟨v, hv⟩ i)

theorem exists_sec_iso {X X' : Scheme.{0}} {β : X' ⟶ X} {M : LB X} {M' : LB X'} (hM : M.IsLB) (hM' : M'.IsLB)
    (w : LB.Iso M' (M.pull β)) (hw : w.IsGen) (s : LB.Sec M') :
    ∃ t : LB.Sec (M.pull β), ∀ z k k', β z ∈ M.U k → z ∈ M'.U k' →
      gs (𝟙 X') z _ (t.f fun _ => k) = (Geo.Tor.gw w (𝟙 _) z k k').val * gs (𝟙 X') z _ (s.f k') := by
  refine ⟨SecOn.topEquiv _ (SecOn.congr hM' (LB.isLB_pull hM β) w hw ⊤ ((SecOn.topEquiv M').symm s)),
    fun z k k' hk hk' => ?_⟩
  have hz : z ∈ (M.pull β).U (fun _ => k) ⊓ M'.U k' := ⟨mem_pull.2 hk, hk'⟩
  have e := congrArg (gs (𝟙 X') z _) (SecOn.coord_congr hM' (LB.isLB_pull hM β) w hw
    ((SecOn.topEquiv M').symm s) (fun _ => k) k' (le_inf le_top inf_le_left) (le_inf le_top inf_le_right) le_rfl)
  rw [gs_mul _ _ _ hz, gs_res _ _ _ hz, gs_res _ _ _ hz, gs_res _ _ _ hz] at e
  refine (gs_res _ _ _ hz.1 _).trans (e.trans (congrArg₂ (· * ·) (gs_unit _ _ _ hz _) ?_))
  exact gs_res (𝟙 X') z (inf_le_right : ⊤ ⊓ M'.U k' ≤ _) ⟨trivial, hk'⟩ (s.f k')

theorem gs_comb {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (z : X)
    {U : X.Opens} (h : z ∈ U) {n : ℕ} (c : Fin n → R) (x : Fin n → Γ(X, U)) :
    gs (𝟙 X) z U (∑ j, AbLaw.cst f U (c j) * x j) = ∑ j, gs (𝟙 X) z ⊤ (AbLaw.cst f ⊤ (c j)) * gs (𝟙 X) z U (x j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [gs_eq _ _ _ h, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← gs_eq _ _ _ h, gs_mul _ _ _ h, ← rs_cst f (le_top : U ≤ ⊤), gs_res _ _ _ h]

theorem loc_mulVec {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (P : Perf f M) (π : X' ⟶ X)
    (f' : X' ⟶ Spec (CommRingCat.of R')) {n : ℕ} (B : Matrix (Fin P.a) (Fin n) R') (c : Fin n → R') (i : P.I) :
    Seesaw.loc P π f' (B.mulVec c) i = ∑ j, AbLaw.cst f' _ (c j) * Seesaw.loc P π f' (fun k => B k j) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Seesaw.loc, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem exists_basis : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → IsProjBy f → ∀ M : LB X, M.IsLB → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (M₀ : LB X₀) (w₀ : LB.Iso M₀ (M.pull π)), M₀.IsLB → w₀.IsGen → FirstCohomologyVanishes M₀ → ∃ (n : ℕ) (τ : Fin n → LB.Sec M), ∀ (A' : Type) [CommRing A'] (g : A →+* A') (X' : Scheme.{0}) (β : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of A')), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (M' : LB X') (w : LB.Iso M' (M.pull β)) (τ' : Fin n → LB.Sec M'), M'.IsLB → w.IsGen → (∀ i, (∀ z (k : (M).ι) (k' : (M').ι), (β) z ∈ (M).U k → z ∈ (M').U k' → gs (β) z _ ((τ i).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((τ' i).f k'))) → ∀ s' : LB.Sec M', ∃! c : Fin n → A', ∀ k : M'.ι, s'.f k = ∑ i, AbLaw.cst f' (M'.U k) (c i) * (τ' i).f k := by
  intro A _ _ _ X f hf hp M hM K _ g₀ hg₀ X₀ π f₀ h₀ M₀ w₀ hM₀ hw₀ hH
  obtain ⟨P⟩ := nonempty_perf_of_noetherian A X f hf hp M hM
  obtain ⟨w₁, hw₁⟩ := LBIso.symm (⟨w₀, hw₀⟩ : LBIso _ _)
  obtain ⟨r, n, B, hr, hB, hu⟩ := exists_matrix_basis_ker_of_exact_at_point A K g₀ _ _ _ P.D₀ P.D₁
    P.comp (P.exact K g₀ X₀ π f₀ h₀ (H1Iso.firstCohomologyVanishes_of_iso_of_isGen hM₀.cover (LB.isLB_pull hM π) w₁ hw₁ hH))
  have hru : IsUnit r := by
    by_contra hn
    have := IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective g₀ hg₀)
    exact hr ((RingHom.mem_ker).1 (this ▸ (show r ∈ IsLocalRing.maximalIdeal A from hn)))
  choose τ hτ using fun j => exists_sec_of_ker P (fun k => B k j) (funext fun l => congrFun₂ hB l j)
  refine ⟨n, τ, fun A' _ g X' β f' h M' w τ' hM' hw hτ' s' => ?_⟩
  obtain ⟨E, hE⟩ := P.sec A' g X' β f' h
  obtain ⟨t, ht⟩ := exists_sec_iso hM hM' w hw s'
  obtain ⟨v, rfl⟩ := E.surjective t
  have hA : ∀ z i k', β z ∈ P.W i → z ∈ M'.U k' → gs (𝟙 X') z _ (Seesaw.loc P β f' v.1 i) =
      (Geo.Tor.gw w (𝟙 _) z (P.ch i) k').val * gs (𝟙 X') z _ (s'.f k') := fun z i k' hi hk' =>
    (congrArg (gs (𝟙 X') z _) (hE v i).symm).trans ((gs_res (𝟙 X') z (le_pull M β (P.le i)) hi _).trans (ht z _ k' (P.le i hi) hk'))
  have hC : ∀ (c : Fin n → A') z i k', β z ∈ P.W i → z ∈ M'.U k' →
      gs (𝟙 X') z _ (Seesaw.loc P β f' ((B.map g).mulVec c) i) =
      (Geo.Tor.gw w (𝟙 _) z (P.ch i) k').val *
        gs (𝟙 X') z _ (∑ j, AbLaw.cst f' (M'.U k') (c j) * (τ' j).f k') := fun c z i k' hi hk' => by
    rw [loc_mulVec, gs_comb f' z (show z ∈ β ⁻¹ᵁ P.W i from hi), gs_comb f' z hk', Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm, ← hτ' j z _ k' (P.le i hi) hk']
    refine congrArg (_ * ·) ?_
    refine (congrArg (gs (𝟙 X') z _) (Seesaw.loc_comp P h (fun k => B k j) i)).trans ?_
    rw [← hτ j i]
    refine (gs_pull (𝟙 X') β z _ hi _).trans ?_
    rw [Category.id_comp]
    exact gs_res β z _ hi _
  refine (existsUnique_congr fun c => ⟨fun hc k' => fn_ext fun z hz => ?_, fun hc => ?_⟩).1
    (hu A' g (hru.map g) v.1 v.2)
  · obtain ⟨i, hi⟩ := Seesaw.exists_mem P (β z)
    have e := hC c z i k' hi hz
    rw [hc, hA z i k' hi hz] at e
    exact (Units.mul_right_inj _).1 e
  · have hk : (P.D₀.map g).mulVec ((B.map g).mulVec c) = 0 := by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hB, Matrix.map_zero _ (map_zero g), Matrix.zero_mulVec]
    refine congrArg Subtype.val (E.injective (a₁ := ⟨_, hk⟩) (a₂ := v) ?_)
    refine Seesaw.sec_ext _ _ (fun i => β ⁻¹ᵁ P.W i) (fun i _ => P.ch i) (fun i => le_pull M β (P.le i))
      (fun y => Seesaw.exists_mem P (β y)) fun i => ?_
    refine (hE ⟨_, hk⟩ i).trans (Eq.trans (fn_ext fun z hz => ?_) (hE v i).symm)
    obtain ⟨k', hk'⟩ := exists_chart hM' z
    exact (hC c z i k' hz hk').trans ((congrArg (fun x => _ * gs (𝟙 X') z _ x) (hc k').symm).trans
      (hA z i k' hz hk').symm)

end GlobalTheory.SecBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionIsometryTwistByRootsOfDataIsoStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionIsometry_twistByRoots_of_dataIso : BrGtSt → BrWpSt → AllD fun {E} _ _ _ {H} D => letI := H.starRing; ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (A : ArcF D R F) (D' : DegPre R') [Module (𝓞 E) D'.X] (oa' : D'.OAct (𝓞 E)), D'.PsiEven → D'.TauBimult → ∀ (N' : NumD F) (ν' : NumOf D' F N') (k : ℕ) (β : A.N.Form k) (u : Fˣ) (r : ℕ → Fˣ) (J : NumD.Iso (A.N.twist β u) N'), Roots u r → ActCompat A.ν A.oa ν' oa' β u r J → ∃ I' : TateIsoQ D D' oa' F, I'.ζ = A.I.ζ ∧ ∀ j, 0 < j → ∀ x, ∃ q', TwJ β u (r j) J (A.q j x) q' ∧ ν'.QPt (I'.ev j x) q' := by
  first | exact @GlobalTheory.Relabel.exists_tateIsoQ_twJ | exact GlobalTheory.Relabel.exists_tateIsoQ_twJ | (intros; apply GlobalTheory.Relabel.exists_tateIsoQ_twJ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyAlgebraisationFormalTowerAmple
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.TowerAlg

theorem isPullback_of_grp {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [GrpObj B'] {f : S' ⟶ S}
    {F : B'.left ⟶ B.left} (h : IsGrpPullback B' B f F) : IsPullback F B'.hom B.hom f := h.1

theorem exists_alg (hG : GlobalFnsSt) (hE : Ega) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
    (hA : admitted R I) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)]
    [∀ e, IsCommMonObj (Y e)] (hY : ∀ e, IsAbelianScheme (Y e)) (N : ∀ e, CP (Y e))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (h : ∀ e, IsCPPullback (N e) (N (e + 1)) (thickTrans R I e) (β e))
    (hamp : RelAmple (Y 0) (N 0).L.L) :
    ∃ (B : Over (Spec (CommRingCat.of R))) (_ : GrpObj B) (_ : IsCommMonObj B) (Q : CP B)
      (b : ∀ e, (Y e).left ⟶ B.left), IsAbelianScheme B ∧ RelAmple B Q.L.L ∧
      (∀ e, IsCPPullback (N e) Q (thick R I e) (b e)) ∧ ∀ e, β e ≫ b (e + 1) = b e := by
  have hN : IsNoetherianRing R := hA.1.1
  have hI : I ≠ ⊤ := hA.2.2.2.1.ne_top
  have hc : IsAdicComplete I R := hA.1.2.2.2
  choose hβ v hv using h
  obtain ⟨B, M, b, hp, hs, hM, ha, hb, hβb, hiso⟩ := hE.1 R I hI hc hA.2.1 Y β
    (fun e => (N e).L.L) v (fun e => isPullback_of_grp (hβ e)) (fun e => (hY e).smooth)
    (fun e => ⟨(N e).L.isLB, (hv e).gen⟩) hamp
  obtain ⟨g, hB, hg⟩ := _root_.GlobalTheory.AlgGroup.isAbelianScheme_of_thickenings hE R I hA Y β hY hβ B b hp hs hb hβb
  have c := hB.comm
  obtain ⟨Q, hQ, hq⟩ := exists_cp_alg hG hE.2.2.1 hI hc N hB hp hg hM hiso hY
  exact ⟨B, g, c, Q, b, hB, by rw [hQ]; exact ha, hq, hβb⟩

theorem nonempty_alg : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G) (X : Type) [AddCommGroup X] (T : TowerR I P X), RelAmple (T.l 0).Q.B (T.l 0).D.M.L.L → Nonempty T.Alg := by
  intro hL _ hE R _ _ _ I hA G _ _ P X _ T hamp
  obtain ⟨B, _, _, Q, b, h₁, h₂, h₃, h₄⟩ := exists_alg hL.globalFns hE hA (fun e => (T.l e).Q.B)
    (fun e => (T.l e).Q.isAb) (fun e => (T.l e).D.M) T.β T.β_pb hamp
  exact ⟨⟨B, h₁, Q, h₂, b, h₃, h₄⟩⟩

end GlobalTheory.TowerAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormalisedRosatiGeneratorValuesMoveAlongIsoStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedRosatiGenerator_values_move_along_iso : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (D : DegPre R) (D' : DegPre R') (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (O : Type) [CommRing O] [StarRing O] (oa : D.P.OAct O) (oa' : D'.P.OAct O) (Φ : (TF (R := R) F ⊗ D.P.A).left ⟶ D'.P.A.left) (w : LB.Iso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left) (D'.P.L.pull Φ)) (φ : N.A →* N'.A) (wv : N.A → F), w.IsGen → Φ ≫ D'.P.A.hom = (fst (TF (R := R) F) D.P.A).left ≫ (TF (R := R') F).hom → (∀ x, (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ Φ = (ν'.eA (φ x)).left) → (∀ x, wv x = valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _ (w.s (fun _ => ν'.J (ν'.eA (φ x)).left, fun _ => ν.J (ν.eA x).left)).val) → (∀ y b, φ (actV ν oa y b) = actV ν' oa' y (φ b)) → ∀ (a : O) ρ ρ', RosV ν oa a ρ → RosV ν' oa' a ρ' → ∀ b b', ρ' (φ b) (φ b') * (wv (actV ν oa (star a) b) * wv b' * wv (b * actV ν oa a b')) = ρ b b' * (wv (actV ν oa (star a) b * b') * wv b * wv (actV ν oa a b')) := by
  first | exact @GlobalTheory.RosMove.rosV_move | exact GlobalTheory.RosMove.rosV_move | (intros; apply GlobalTheory.RosMove.rosV_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedAVIsoDescendsOfRationalThreeTorsionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedAVIso_descends_of_rational_threeTorsion : Laws → Laws2 → GlobalTheory.LN.HomExtSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (C : Type) [Field C] [IsAlgClosed C] [Algebra (FractionRing R) C] (B B' : PolAV (Sp R)), RatTors B C 3 → RatTors B' C 3 → ∀ (φ : TF (R := R) C ⊗ B.A ≅ TF (R := R) C ⊗ B'.A) (g : (TF (R := R) C ⟶ B.A) ≃* (TF (R := R) C ⟶ B'.A)), φ.hom ≫ fst _ _ = fst _ _ → (∀ x, lift (𝟙 _) x ≫ φ.hom = lift (𝟙 _) (g x)) → LBIso (B.L.pull (snd (TF (R := R) C) B.A).left) (B'.L.pull (φ.hom ≫ snd (TF (R := R) C) B'.A).left) → ∃ Ψ : B'.A ≅ B.A, IsMonHom Ψ.hom ∧ LBIso B'.L (B.L.pull Ψ.hom.left) ∧ ∀ x, g x ≫ Ψ.hom = x := by
  first | exact @GlobalTheory.polAV_iso_descends_of_ratTors | exact GlobalTheory.polAV_iso_descends_of_ratTors | (intros; apply GlobalTheory.polAV_iso_descends_of_ratTors <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionQuotientActionCompatOfRosatiValuesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionQuotientAction_compat_of_rosatiValues : GlobalFnsSt → BrGtSt → AllD fun {E} _ _ _ {H} D => letI := H.starRing; ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (A : ArcF D R F) (D' : DegPre R') [Module (𝓞 E) D'.X] (oa' : D'.OAct (𝓞 E)), D'.PsiEven → D'.TauBimult → ∀ (N' : NumD F) (ν' : NumOf D' F N') (k : ℕ) (β : A.N.Form k) (u : Fˣ) (r : ℕ → Fˣ) (J : NumD.Iso (A.N.twist β u) N'), Roots u r → A.Bal β → (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.act x y)) = x • ν'.eX (J.e y)) → (∀ (x : 𝓞 E) b, J.φ (actV (N := A.N) A.ν A.oa.onB x b) = actV ν' oa'.onB x (J.φ b)) → (∀ a : 𝓞 E, ∃ ρ ρ', RosV A.ν A.oa.onB a ρ ∧ RosV ν' oa'.onB a ρ' ∧ ∀ b b' : A.N.A, ρ' (J.φ b) (J.φ b') * (J.h (actV (N := A.N) A.ν A.oa.onB (star a) b) * J.h b' * J.h (b * actV (N := A.N) A.ν A.oa.onB a b') : Fˣ) = ρ b b' * (J.h (actV (N := A.N) A.ν A.oa.onB (star a) b * b') * J.h b * J.h (actV (N := A.N) A.ν A.oa.onB a b') : Fˣ)) → ActCompat A.ν A.oa ν' oa' β u r J := by
  first | exact @GlobalTheory.Relabel.actCompat_of_rosV | exact GlobalTheory.Relabel.actCompat_of_rosV | (intros; apply GlobalTheory.Relabel.actCompat_of_rosV <;> assumption)
end

