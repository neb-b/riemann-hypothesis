module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilySimilitudeGroupActionFreeTransitive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2034
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1952
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSinglePolarisationGeneratorAllTraits
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2671
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2483
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2586
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2521
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2632
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelCoverMatrices
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor GlobalTheory.SiegLevCalc
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SiegLevCover


set_option maxHeartbeats 1000000 in
theorem exists_levelCover : ∀ (g n ℓ j : ℕ) (F : SFam g n (zetaAway n)), 1 ≤ g → 3 ≤ n → Odd n → ℓ.Prime → ℓ ∣ n →
    1 ≤ j →
    ∃ (κ : cycAway n →+* cycAway (n * (ℓ ^ j) ^ 2)) (F' : SFam g (n * (ℓ ^ j) ^ 2) (zetaAway (n * (ℓ ^ j) ^ 2)))
      (q : F'.X ⟶ F.X),
      (Function.Injective κ ∧ κ (zetaAway n) = zetaAway (n * (ℓ ^ j) ^ 2) ^ ((ℓ ^ j) ^ 2) ∧ IsFinite (spMap κ) ∧
        Etale (spMap κ) ∧ Surjective (spMap κ)) ∧
      (q ≫ F.s = F'.s ≫ spMap κ ∧ IsFinite q ∧ Etale q ∧ Surjective q ∧ SRel F'.univ F.univ ((ℓ ^ j) ^ 2) 1 q) ∧
      ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (ρ : Γ → (F'.X ⟶ F'.X)) (ν : Γ → (F'.univ.A.left ⟶ F'.univ.A.left)),
        ρ 1 = 𝟙 _ ∧ (∀ a b, ρ (a * b) = ρ a ≫ ρ b) ∧ ν 1 = 𝟙 _ ∧ (∀ a b, ν (a * b) = ν a ≫ ν b) ∧
        (∀ a, SRelBy F'.univ F'.univ ((ℓ ^ j) ^ 2) ((ℓ ^ j) ^ 2) (ρ a) (ν a)) ∧ (∀ a, ρ a ≫ q = q) ∧
        ∀ (K : Type) [Field K] [IsAlgClosed K] (x y : Sp K ⟶ F'.X), x ≫ q = y ≫ q → ∃! a, x ≫ ρ a = y := by
  intro g n ℓ j F hg hn hodd hℓ hℓn hj
  have hn0 : n ≠ 0 := by omega
  have hd0 : (ℓ ^ j) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have hN0 : n * (ℓ ^ j) ^ 2 ≠ 0 := Nat.mul_ne_zero hn0 hd0
  have hnN : n ∣ n * (ℓ ^ j) ^ 2 := dvd_mul_right n _
  have hNn : n * (ℓ ^ j) ^ 2 / n = (ℓ ^ j) ^ 2 := Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn0)
  have hℓodd : Odd ℓ := Odd.of_dvd_nat hodd hℓn
  have hNodd : Odd (n * (ℓ ^ j) ^ 2) := hodd.mul (hℓodd.pow.pow)
  have hN3 : 3 ≤ n * (ℓ ^ j) ^ 2 := le_trans hn (Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero hd0))
  have hpow : ∃ a, n * (ℓ ^ j) ^ 2 ∣ n ^ a := ⟨2 * j + 1, by
    rw [pow_succ' n (2 * j)]
    refine mul_dvd_mul_left n ?_
    rw [← pow_mul, mul_comm j 2]
    exact pow_dvd_pow_of_dvd hℓn _⟩
  obtain ⟨κ, hinj, hζ, hfes⟩ := GlobalTheory.SiegelTor.exists_inclusion_cycAway n (n * (ℓ ^ j) ^ 2) hN0 hnN
  obtain ⟨hfin, het, hsurj⟩ := hfes hpow
  obtain ⟨F'⟩ := GlobalTheory.SiegelTor.exists_sFam_cycAway g (n * (ℓ ^ j) ^ 2) hg hN3 hNodd
  obtain ⟨Q⟩ := GlobalTheory.SiegLev.nonempty_sQuot g n _ F' κ hn hNodd hnN hζ hfin het
  let Fq : SFam g n (zetaAway n) :=
    { X := Q.X
      s := Q.s
      smooth := Q.smooth
      qproj := Q.qproj
      univ := Q.univ
      princ := Q.princ
      rep := fun S s' c hred hdense hpr =>
        GlobalTheory.quotFam_represents g n _ F' κ Q hn hNodd hnN hinj hζ hfin het hsurj S s' c hred hdense hpr
      inj := fun R _ _ x y s' c hs h₁ h₂ =>
        GlobalTheory.SiegLev.SQuot.eq_of_siegPB g n _ _ _ (zetaAway n) (zetaAway _) F' κ Q R x y s' c hs h₁ h₂ }
  obtain ⟨e, he, hpb⟩ := SFam.exists_iso Fq F
  obtain ⟨Ga, _, _, ρ, ν, h1, hmul, hν1, hνmul, hbase, hrel, hfree, htrans⟩ :=
    GlobalTheory.SiegAct.siegel_group_action g n _ F' κ hn hNodd hnN hζ
  rw [hNn] at hζ hrel htrans
  have hlow : SRel F'.univ Q.univ ((ℓ ^ j) ^ 2) 1 Q.π := by
    have := Q.low
    rwa [hNn] at this
  let q : F'.X ⟶ F.X := Q.π ≫ e.hom
  have hqs : q ≫ F.s = F'.s ≫ spMap κ := by
    show (Q.π ≫ e.hom) ≫ F.s = _
    rw [Category.assoc, he]
    exact Q.base
  have hq : SRel F'.univ F.univ ((ℓ ^ j) ^ 2) 1 q :=
    sRel_comp ((sRel_one_one_iff Q.univ F.univ e.hom).2 hpb) hlow
  haveI := Q.fin
  haveI := Q.etale
  haveI := Q.onto
  have hinv : ∀ a, ρ a ≫ q = q := by
    intro a
    obtain ⟨c, hc⟩ := (GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) F.X F'.X F.s (q ≫ F.s) q F.univ rfl).1
    have m1 : SRel c F'.univ 1 ((ℓ ^ j) ^ 2) (𝟙 F'.X) :=
      SiegLevCalc.sRel_cancel (f' := 𝟙 F'.X) hq (by rw [Category.id_comp]; exact (sRel_one_one_iff _ _ _).2 hc)
    have m2 : SRel F'.univ F.univ ((ℓ ^ j) ^ 2) 1 (ρ a ≫ q) := sRel_comp hq ⟨ν a, hrel a⟩
    have m3 := sRel_comp m2 m1
    rw [Category.id_comp, sRel_one_one_iff] at m3
    refine SFam.hom_ext F c _ _ ?_ m3 hc
    rw [Category.assoc, hqs]
    exact hbase a
  refine ⟨κ, F', q, ⟨hinj, hζ, hfin, het, hsurj⟩, ⟨hqs, inferInstance, inferInstance, inferInstance, hq⟩,
    Ga, inferInstance, inferInstance, ρ, ν, h1, hmul, hν1, hνmul, hrel, hinv, ?_⟩
  intro K _ _ x y hxy
  obtain ⟨c, hc⟩ :=
    (GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) F.X (Sp K) F.s ((x ≫ q) ≫ F.s) (x ≫ q) F.univ rfl).1
  have mx : SRel c F'.univ 1 ((ℓ ^ j) ^ 2) x := SiegLevCalc.sRel_cancel hq ((sRel_one_one_iff _ _ _).2 hc)
  have my : SRel c F'.univ 1 ((ℓ ^ j) ^ 2) y := SiegLevCalc.sRel_cancel hq (by rw [← hxy]; exact (sRel_one_one_iff _ _ _).2 hc)
  have hs : x ≫ F'.s ≫ spMap κ = y ≫ F'.s ≫ spMap κ := by
    rw [← hqs, ← Category.assoc, hxy, Category.assoc]
  obtain ⟨a, ha⟩ := htrans K x y _ c hs mx my
  refine ⟨a, ha, fun b hb => ?_⟩
  have hy : y ≫ ρ (a⁻¹ * b) = y := by
    calc y ≫ ρ (a⁻¹ * b) = x ≫ ρ (a * (a⁻¹ * b)) := by rw [hmul a, ← ha, Category.assoc]
      _ = y := by rw [mul_inv_cancel_left, hb]
  exact (inv_mul_eq_one.1 (hfree K y _ hy)).symm

end GlobalTheory.SiegLevCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionClosedFibreOfPrimitiveTheta
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.OmDvr

theorem exists_unit_of_prim {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {J : Type}
    {c : J → FractionRing V} (b : FractionRing V) (hc : Prim (algebraMap V (FractionRing V)) c)
    (hb : Prim (algebraMap V (FractionRing V)) (fun j => b * c j)) :
    ∃ u : Vˣ, algebraMap V (FractionRing V) u = b := by
  obtain ⟨hc₁, j₀, hj₀, hj₀'⟩ := hc
  obtain ⟨hb₁, j₁, hj₁, hj₁'⟩ := hb
  have I1 : IsIntegral V b := by
    have := IsIntegral.mul (show IsIntegral V (b * c j₀) from hb₁ j₀) (show IsIntegral V (c j₀)⁻¹ from hj₀')
    rwa [_root_.mul_assoc, mul_inv_cancel₀ hj₀, _root_.mul_one] at this
  have hcne : c j₁ ≠ 0 := right_ne_zero_of_mul hj₁
  have I2 : IsIntegral V b⁻¹ := by
    have := IsIntegral.mul (show IsIntegral V (c j₁) from hc₁ j₁) (show IsIntegral V (b * c j₁)⁻¹ from hj₁')
    rwa [mul_inv, mul_left_comm, mul_inv_cancel₀ hcne, _root_.mul_one] at this
  obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 I1
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 I2
  have hb0 : b ≠ 0 := left_ne_zero_of_mul hj₁
  have hvw : v * w = 1 := IsFractionRing.injective V (FractionRing V) (by
    rw [map_mul, hv, hw, mul_inv_cancel₀ hb0, map_one])
  exact ⟨⟨v, w, hvw, by rw [mul_comm, hvw]⟩, hv⟩

theorem polAt_of_polFib {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    {g : ℕ} {K : Type} [Field K] {x : Sp K ⟶ S} (h : PolFib t.G t.PP.L g x) : GlobalTheory.LN.PolAt t x := by
  obtain ⟨P, α, -, hp, hw⟩ := h
  have hN := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  obtain ⟨φ, hφ, e, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := 𝟙 _) (f := x)
    ((isGrpPullback_pullback t.G x).congr (Category.id_comp _).symm rfl) hp t.PP.isLB P.isLB hN
    ⟨Out.CubePf.idIsoL _, Out.CubePf.idIsoL_isGen hN⟩ hw
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) hφ.1 P.isAb.proper,
    amplePt _ _ _ _ _ _ hφ _ _ P.isLB hN e P.ample P.ktriv⟩

end GlobalTheory.UMin.OmDvr


set_option maxHeartbeats 1000000 in
open GlobalTheory.UMin.OmDvr in
theorem GlobalTheory.UMin.exists_sec_nz_of_prim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (θ : SecAt t.G t.PP.L (spMap (algebraMap V (FractionRing V)) ≫ χ)) (pt : Fin N → (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ χ) ⟶ t.G)) (c : Fin N → FractionRing V), Odd m → 3 ≤ m → IsUnit (m : V) → PolFib t.G t.PP.L g (spMap (algebraMap V (FractionRing V)) ≫ χ) → ThList t.G t.PP.L t.PP.rig m _ θ pt c → Prim (algebraMap V (FractionRing V)) c → ∃ σ : SecAt t.G t.PP.L χ, SecM.ofSec t.G (SecAt.pull t.G t.PP.L σ (algebraMap V (FractionRing V))) = SecM.ofSec t.G θ ∧ NZ t.G t.PP.L χ σ := by
  intro E _ _ _ H S t g m N V _ _ _ hV χ θ pt c hm h3 hu hP hT hc
  have hL := t.PP.isLB
  have : IsDiscreteValuationRing V := hV.1
  have := t.semi.comm
  have hpa := GlobalTheory.UMin.OmDvr.polAt_of_polFib t hP
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull Out.CubePf.cubePull χ t
  have hp' := GlobalTheory.SplitPoint.polAt_pullback m₁ hpa (jK V) (𝟙 _) (Category.id_comp _).symm
  obtain ⟨σ₀, hσ₀⟩ := exists_nz_of_polAt abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 E H S t V χ _ m₁ hp'
  have h0V : spMap (RingHom.id V) ≫ χ = χ := (congrArg (· ≫ χ) (Spec.map_id _)).trans (Category.id_comp _)
  have hNZ := hσ₀ V (RingHom.id V) χ h0V
  obtain ⟨P, α, hg, hp, hw⟩ := hP
  have hx0 : spMap (RingHom.id (FractionRing V)) ≫ (spMap (algebraMap V (FractionRing V)) ≫ χ) =
      spMap (algebraMap V (FractionRing V)) ≫ χ :=
    (congrArg (· ≫ _) (Spec.map_id _)).trans (Category.id_comp _)
  obtain ⟨e, he⟩ := exists_univBasis_of_fibre abelianSchemeLaws_all.2 S (Sp (FractionRing V)) t.G t.PP.L hL P _ α hp hw
    (FractionRing V) (𝟙 _) _ (Category.id_comp _)
  obtain ⟨a, ha⟩ := he.ex (RingHom.id _) hx0 (SecM.ofSec t.G θ)
  generalize VVRank.pullS t.G _ (Over.homMk (spMap (RingHom.id V)) h0V : Over.mk χ ⟶ Over.mk χ) σ₀ = σ₁ at hNZ
  obtain ⟨s, hs⟩ := he.ex (RingHom.id _) hx0 (pl (algebraMap V (FractionRing V)) rfl (SecM.ofSec t.G σ₁))
  have hmK : ((m : ℕ) : FractionRing V) ≠ 0 := by
    have := (hu.map (algebraMap V (FractionRing V))).ne_zero
    rwa [map_natCast] at this
  obtain ⟨j₀, hj₀, -⟩ := hc.2
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h00 : SecM.ofSec t.G θ = @id Γ((Over.mk (spMap (algebraMap V (FractionRing V)) ≫ χ)).left, ⊤)
        (GlobalTheory.ZH.fn (0 : FractionRing V)) • SecM.ofSec t.G θ := by
      change _ = fnR (spMap (algebraMap V (FractionRing V)) ≫ χ) 0 • _
      rw [map_zero, zero_smul, ha, map_zero, zero_smul]
    have q := (GlobalTheory.UMin.thG_smul_iff S t.G t.PP.L t.PP.rig hL t.PP.rigGen g m (FractionRing V) _ θ θ (pt j₀) 0 (c j₀) (c j₀) hm
      hmK ⟨P, α, hg, hp, hw⟩ h00 (hT.2.1 j₀)).1 (hT.2.1 j₀)
    exact hj₀ (by simpa using q)

  have hrel : pl (algebraMap V (FractionRing V)) rfl (SecM.ofSec t.G σ₁) =
      fnR (spMap (algebraMap V (FractionRing V)) ≫ χ) (s * a⁻¹) • SecM.ofSec t.G θ := by
    have key : s = (s * a⁻¹) * a := by rw [_root_.mul_assoc, inv_mul_cancel₀ ha0, _root_.mul_one]
    rw [hs, ha, smul_smul, ← map_mul, ← key]
  have hT' : ThList t.G t.PP.L t.PP.rig m (spMap (algebraMap V (FractionRing V)) ≫ χ)
      (SecAt.pull t.G t.PP.L σ₁ (algebraMap V (FractionRing V))) pt (fun j => (s * a⁻¹) * c j) := by
    refine ⟨hT.1, fun j => ?_, hT.2.2⟩
    show ThG t.G t.PP.L t.PP.rig m _ (pt j) (fnR (spMap (algebraMap V (FractionRing V)) ≫ χ) ((s * a⁻¹) * c j))
    rw [map_mul]
    exact ThG.smul hL hrel (hT.2.1 j)
  have hprim := GlobalTheory.UMin.prim_of_polFib E H S t g V hV χ ⟨P, α, hg, hp, hw⟩ _ hNZ m N hm h3 hu (FractionRing V)
    (algebraMap V (FractionRing V)) pt _ (IsFractionRing.injective V (FractionRing V)) hT'
  obtain ⟨u, hu'⟩ := exists_unit_of_prim (s * a⁻¹) hc hprim
  have hpull : pl (algebraMap V (FractionRing V)) rfl (fnR χ (u⁻¹ : Vˣ).val • SecM.ofSec t.G σ₁) = SecM.ofSec t.G θ := by
    rw [pl_smul, hrel, smul_smul, ← map_mul, ← hu', ← map_mul, Units.inv_mul, map_one, map_one, one_smul]
  refine ⟨SecM.toSec t.G (fnR χ (u⁻¹ : Vˣ).val • SecM.ofSec t.G σ₁), hpull, ?_⟩
  obtain ⟨g₀, h₁, h₂⟩ := hNZ
  refine ⟨g₀, h₁, ?_⟩
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h₂
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩
  change g₀ ∈ Scheme.basicOpen _ (liftHom t.G _ (fnR χ (u⁻¹ : Vˣ).val) * σ₁.f k)
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (((u⁻¹).isUnit.map (fnR χ)).map (liftHom t.G _))]
  exact ⟨Scheme.basicOpen_le _ _ hk, hk⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOriginNormalisationUnitAtTraits
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_unit_normalisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ Φ : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k, (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F, T.Exp a b (Φ F) F) → ∃ Φ' : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ' F) F := by
  intro R _ _ _ hR D C
  obtain ⟨k₁, hk₁⟩ := _root_.GlobalTheory.Mum.exists_secB_zero_nonzero_origin R hR D
  refine ⟨max k₁ 1, fun k hk Φ hΦ => ?_⟩
  obtain ⟨b₀, hb₀⟩ := hk₁ k (le_of_max_le_left hk)
  have hk1 : 1 ≤ k := le_of_max_le_right hk
  obtain ⟨F₀, hF₀⟩ := (_root_.GlobalTheory.ThFam.exists_intFam_lead R hR D).2 k hk1 b₀
  obtain ⟨c₁, c₂, hc₂, hc⟩ := _root_.GlobalTheory.Mum.exists_norm_const R hR D C k hk1 b₀ hb₀ F₀ hF₀ (Φ F₀)
  refine ⟨fun F => scal C.A.A.hom (algebraMap R (FractionRing R) c₁ / algebraMap R (FractionRing R) c₂) • Φ F,
    fun W _ _ _ T => ?_⟩
  obtain ⟨a, b, ha, hb, hE⟩ := hΦ W T
  obtain ⟨u, hu⟩ := hc W T a b ha hb (hE F₀)
  exact ⟨u, fun F => _root_.GlobalTheory.Mum.Trait.exp_rescale R hR D C W T k (Φ F) F a b u c₁ c₂ ha hc₂ hu (hE F)⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductSmallTwistedFunctionalEqnFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem GlobalTheory.TwFam.exists_prod_family : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (f : ∀ β, SecT D.toPre a n j β) (g : ∀ β, SecT D.toPre a n' j' β), Small (maximalIdeal R) (w := id) f → Small (maximalIdeal R) (w := id) g → TFE h h' f → TFE h h' g → ∃ F : ∀ β, SecT D.toPre a n'' j'' β, Small (maximalIdeal R) (w := id) F ∧ TFE h h' F ∧ ∀ (e : ℕ) (τ : SecE U.toUnifPre (b e) n j) (τ' : SecE U.toUnifPre (b e) n' j'), TExp U.toUnifPre τ (w := id) f → TExp U.toUnifPre τ' (w := id) g → ∃ τ'' : SecE U.toUnifPre (b e) n'' j'', (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' * sval τ' x z J') ∧ TExp U.toUnifPre τ'' (w := id) F := by
  intro R _ _ _ hadm D a a' h h' hED A G _ _ hG U b hb n j n' j' n'' j'' hn hj f g hfs hgs hf hg
  have hP := _root_.GlobalTheory.TwFam.exists_prodT_van R hadm D a n j n' j' n'' j'' hn hj
  choose p hpP hpV using fun q : D.toPre.X × D.toPre.X => hP q.1 q.2 (f q.1) (g q.2)
  have hps : Small (maximalIdeal R) (w := fun q : D.toPre.X × D.toPre.X => q.1 + q.2) p := by
    intro e
    refine ((hfs e).prod (hgs e)).subset ?_
    intro q hq
    by_contra hc
    simp only [Set.mem_prod, Set.mem_setOf_eq, not_and_or, not_not] at hc
    exact hq (hpV q e hc)
  obtain ⟨F, hFs, hFsm⟩ := GlobalTheory.T.exists_adicSum_twistedSectionFamily_tendsToZero R hadm D a n'' j'' (D.toPre.X × D.toPre.X) (fun q => q.1 + q.2) p hps
  refine ⟨F, hFsm, ?_, ?_⟩
  · let σ : D.toPre.X → (D.toPre.X × D.toPre.X) ≃ (D.toPre.X × D.toPre.X) := fun mu =>
      Equiv.prodCongr (Equiv.addRight (shift h h' n j mu)) (Equiv.addRight (shift h h' n' j' mu))
    have hσw : ∀ mu q, (σ mu q).1 + (σ mu q).2 = q.1 + q.2 + shift h h' n'' j'' mu := by
      intro mu q
      subst hn hj
      simp only [σ, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.coe_addRight, shift, add_smul]
      abel
    have hσr : ∀ (mu : D.toPre.X) (q : D.toPre.X × D.toPre.X), TRel h mu (p q) (p (σ mu q)) := fun mu q =>
      _root_.GlobalTheory.TwFam.ProdRel.trel_prod R hadm D a a' h h' hED n j n' j' n'' j'' hn hj mu q.1 q.2 (σ mu q).1 (σ mu q).2
        (f q.1) (g q.2) (p q) (f _) (g _) (p (σ mu q)) rfl rfl (hpP q) (hpP (σ mu q)) (hf mu q.1) (hg mu q.2)
    exact _root_.GlobalTheory.TwFam.SumFE.tfe_of_isSum R hadm D a a' h h' hED n'' j'' (D.toPre.X × D.toPre.X) (fun q => q.1 + q.2) p F σ
      hps hFs hσw hσr
  · intro e τ τ' hτ hτ'
    have hform : FormEq
        (Sum.elim ![(fstG (maximalIdeal R) e G).left, (b e).left ≫ (fstG (maximalIdeal R) e G).left]
          ![(fstG (maximalIdeal R) e G).left, (b e).left ≫ (fstG (maximalIdeal R) e G).left])
        (Sum.elim ![n, j] ![n', j'])
        ![(fstG (maximalIdeal R) e G).left, (b e).left ≫ (fstG (maximalIdeal R) e G).left] ![n'', j''] := by
      intro V _ k
      rw [Fintype.prod_sum_type]
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Sum.elim_inl,
        Sum.elim_inr, hn, hj, zpow_add]
      exact mul_mul_mul_comm _ _ _ _
    obtain ⟨τ'', hτ''⟩ := exists_sec U.LG.isLB hform (H1.SectionArithmetic.mulSec τ τ')
    have hmul : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'),
        Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' * sval τ' x z J' := fun Z x z J' hJ =>
      (hτ'' Z x z J' hJ).trans (H1.SectionArithmetic.sval_mulSec τ τ' x z hJ)
    exact ⟨τ'', hmul, GlobalTheory.T.twistedExpansion_adicSums_admissibleBase R hadm D a A G hG U e (b e) n'' j'' τ'' (D.toPre.X × D.toPre.X)
      (fun q => q.1 + q.2) p F hps hFs
      (GlobalTheory.T.twistedExpansion_mul_of_memberProducts R hadm D a A G hG U e (b e) n j n' j' n'' j'' hn hj f g p τ τ' τ'' hfs hgs hpP hτ hτ' hmul)⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackIntegralExpansionFormalEndomorphis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem exists_pull_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (k : ℕ) (σ : H0 U.LG.L k) (f : IntFam (maximalIdeal R) D.toPre k), (∀ e, U.ExpandsAt e k σ f.f) → ∃ ρ : ∀ β, SecT D.toPre a 0 k β, Small (maximalIdeal R) (w := id) ρ ∧ TFE h h' ρ ∧ ∀ e, ∃ τ : SecE U.toUnifPre (b e) 0 k, (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ x z J' = sval σ (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left) z J') ∧ TExp U.toUnifPre τ (w := id) ρ := by
  intro R _ _ _ hR D a a' h h' hE A G _ _ hG U b hb k σ f hσ
  choose u hu using _root_.GlobalTheory.TwFam.exists_iota R hR D a a' h h' hE
  choose s hs hv using fun α => _root_.GlobalTheory.TwFam.exists_isPullT R hR D a k α (h' α) (u α) (f.f α) (hu α).1
  have hsm : Small (maximalIdeal R) (w := fun α => h' α) s := fun e =>
    (f.small e).subset fun α hα hf => hα (hv α e hf)
  obtain ⟨ρ, hρ, hρs⟩ := GlobalTheory.T.exists_adicSum_twistedSectionFamily_tendsToZero R hR D a 0 k _ (fun α => h' α) s hsm
  refine ⟨ρ, hρs, _root_.GlobalTheory.TwFam.SumFE.tfe_of_isSum R hR D a a' h h' hE 0 k _ (fun α => h' α) s ρ
    (fun mu => Equiv.addRight (k • h mu)) hsm hρ (fun mu i => by simp [shift])
    (fun mu i => _root_.GlobalTheory.TwFam.PullRel.main R hR D a a' h h' hE k f mu i _ _ _ _ (hu _) (hu _) (hs _) (hs _)), fun e => ?_⟩
  have hL : U.LG.L.IsLB := U.LG.isLB
  have h1 : (LB.oneGen U.LG.L (Y := (thickObj R (maximalIdeal R) e G).left)).IsGen := fun _ _ =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
  obtain ⟨τ, hτ⟩ := exists_sec hL (K' := Fin 2)
    (φ' := ![(fstG (maximalIdeal R) e G).left, (b e).left ≫ (fstG (maximalIdeal R) e G).left]) (ε' := ![(0 : ℤ), (k : ℤ)])
    (fun V _ g => by simp [Fintype.prod_sum_type, Fin.prod_univ_two])
    (pullMulSec σ ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (LB.oneGen U.LG.L) h1)
  have key : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' →
      sval τ x z J' = sval σ (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left) z J' := fun Z x z J hJ => by
    rw [hτ Z x z J hJ, sval_pullMulSec _ _ _ _ _ _ hJ, val_one, Units.val_one, _root_.mul_one]
  exact ⟨τ, key, GlobalTheory.T.twistedExpansion_adicSums_admissibleBase R hR D a A G hG U e (b e) 0 k τ _ (fun α => h' α) s ρ hsm hρ
    (_root_.GlobalTheory.TwFam.texp_pull R hR D a a' h h' hE A G hG U b hb k e σ f.f u s τ (hσ e) hu hs key)⟩

end GlobalTheory.TwFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutTorsorNTorsionCharacter
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem exists_pushout_torsor (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A]
    (n : ℕ) (hn : (n : R) = 0) (hR : HasRoots A n) (b : Fn0 A) (hb : IsTorsChar n b) :
    ∃ (u : Fn1 A) (g : Fn2 A), IsCoc (whole A) u ∧ IsAdd u g ∧
      ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), (x ^ n : Pt A D) = 1 →
        chi n g D x = b D x := by
  have hSec := _root_.GlobalTheory.PtExt.PushSec.exists_isSec R A n hR b hb
  let S : SecFam A := fun D _ _ x ↦ Classical.choose (hSec D x)
  have hS : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x) :=
    fun D _ _ x ↦ Classical.choose_spec (hSec D x)
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.PtExt.exists_isSecDiff R A n hR b hb S hS
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_sectionAddition_two_point_function R A n hR b hb S hS
  exact ⟨u, g, isCoc_of_isSecDiff R A n hR b hb S hS u hu,
    isAdd_of_isSecDiff_isSecAdd R A n hR b hb S hS u g hu hg,
    chi_eq_of_torsion R A n hn hR b hb S hS g hg⟩

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianVarietyByFiniteSubgroup
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_quotient_finite :
    ∀ (K : Type) [Field K] (A : AbVar K) (H : Over (Sp K)) [GrpObj H] (i : H ⟶ A.X), IsMonHom i → Mono i →
      IsFinite H.hom → ∃ (B : AbVar K) (q : A ⟶ B), IsIsogeny q ∧
        ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ q.hom = 1 ↔ ∃ y, y ≫ i = x := by
  intro K _ A H _ i hi hmono hfin
  have hflat : Flat H.hom := inferInstance
  obtain ⟨B', inst, q, -, hB, hq, hqfin, -, hqsurj, -, hsq⟩ :=
    AbQuotientAny.exists_quotient_abelianScheme K A.X H i A.ab hi hmono hfin hflat
  obtain ⟨g, hg⟩ := GlobalTheory.T.abelianScheme_field_smoothOfRelativeDimension_exists K B' hB
  let B : AbVar K := ⟨B', hB, g, hg⟩
  refine ⟨B, Hom.mk (B := B) q, ⟨hqfin, hqsurj⟩, fun T x => ⟨fun hx => ?_, ?_⟩⟩
  · have e : x ≫ q = (1 : T ⟶ A.X) ≫ q := by
      rw [MonObj.one_comp]; exact hx
    have h1 := hsq.lift_fst x 1 e
    have h2 := hsq.lift_snd x 1 e
    rw [MonObj.comp_mul, h2, _root_.mul_one, ← Category.assoc] at h1
    exact ⟨_, h1⟩
  · rintro ⟨y, rfl⟩
    have hw := congrArg (fun f => lift y (1 : T ⟶ A.X) ≫ f) hsq.w
    rw [← Category.assoc, ← Category.assoc, MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst,
      _root_.mul_one] at hw
    rw [MonObj.one_comp] at hw
    exact hw

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTheoremOfSquareSemiAbelianGenericAbelianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theorem_of_square_semiAbelian_genericAbelian : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSemiAbelian G' → IsAbelianScheme ((Over.pullback (jK R')).obj G') → ∀ N : LB G'.left, N.IsLB → ∀ a : 𝟙_ (Over (Sp R')) ⟶ G', ∃ t : LB.Gen (LB.LinComb N (K := Fin 3) ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left] ![1, 1, -2]), t.IsGen := by
  first | exact @GlobalTheory.SquareGeneric.exists_gen_square | exact GlobalTheory.SquareGeneric.exists_gen_square | (intros; apply GlobalTheory.SquareGeneric.exists_gen_square <;> assumption)
end

