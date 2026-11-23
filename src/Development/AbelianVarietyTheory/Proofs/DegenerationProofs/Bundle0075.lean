module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulPullSec
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ProjZeroPullbackNeZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical

namespace GlobalTheory.ThetaInvPart

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem diag_eq [IsDomain o] {Q : Type} [AddCommGroup Q] [Fintype Q] (π : S.Gam →+ Q) (i₀ : S.J)
    (hc : Fintype.card S.J = Fintype.card Q)
    (hfix : ∀ a, π a = 0 → ∀ l, S.ρ a l i₀ = if l = i₀ then 1 else 0)
    (horb : ∀ i, ∃ a, ∃ e : ℕ, ∀ l, S.ρ a l i₀ = if l = i then S.ζ ^ e else 0) (a : S.Gam) :
    S.ρ a i₀ i₀ = if π a = 0 then 1 else 0 := by
  have hζ : S.ζ ≠ 0 := S.prim.ne_zero (pow_ne_zero _ (Nat.mul_ne_zero (by have := S.r_pos; omega)
    (by have := S.N_ge; omega)))
  choose c e hce using horb
  have key : ∀ a b, π a = π b → ∃ k : ℕ, ∀ l, S.ρ b l i₀ = S.ζ ^ k * S.ρ a l i₀ := fun a b h => by
    obtain ⟨k, hk⟩ := S.ρ_mul b (a - b)
    refine ⟨k, fun l => ?_⟩
    have := congrFun (congrFun hk l) i₀
    rw [Matrix.mul_apply, add_sub_cancel, Matrix.smul_apply, smul_eq_mul] at this
    simpa [hfix (a - b) (by rw [map_sub, h, sub_self])] using this
  have inj : Function.Injective fun i => π (c i) := fun i j h => by
    obtain ⟨k, hk⟩ := key _ _ h
    by_contra hij
    have := hk j
    rw [hce, hce, if_pos rfl, if_neg (Ne.symm hij), mul_zero] at this
    exact pow_ne_zero _ hζ this
  have surj := ((Fintype.bijective_iff_injective_and_card _).2 ⟨inj, hc⟩).2
  have zero : ∀ a i, π (c i) = π a → i ≠ i₀ → S.ρ a i₀ i₀ = 0 := fun a i h hi => by
    obtain ⟨k, hk⟩ := key _ _ h
    rw [hk, hce, if_neg (Ne.symm hi), mul_zero]
  split_ifs with ha
  · rw [hfix a ha, if_pos rfl]
  · obtain ⟨i, hi⟩ := surj (π a)
    refine zero a i hi fun h => ?_
    obtain ⟨j, hj⟩ := surj (π 0)
    by_cases h' : j = i₀
    · exact ha (by rw [← hi, h, ← h', hj, map_zero])
    · have := zero 0 j hj h'
      rw [hfix 0 (map_zero π), if_pos rfl] at this
      exact one_ne_zero this

theorem rho_fix (hG : GlobalFnsSt) (hi : Function.Injective (algebraMap o Ω)) (ρ : S.Real) (a : S.Gam)
    (ha : (ρ.n ^ ρ.k) • S.r • a = 0) (l : S.J) : S.ρ a l ρ.i₀ = if l = ρ.i₀ then 1 else 0 := by
  have := ρ.P.isAb.comm
  have h0 : ρ.pt 0 = 1 := by
    have := ρ.pt_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hp : ∀ (n : ℕ) b, ρ.pt (n • b) = ρ.pt b ^ n := fun n b => by
    induction n with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]
  have hm : ρ.pt (S.r • a) ^ (ρ.n ^ ρ.k) = 1 := by rw [← hp, ha, h0]
  have hN : ρ.pt (S.r • a) ^ S.N = 1 :=
    (congrArg _ (ρ.N_eq.trans (sq _))).trans (by rw [pow_mul, hm, one_pow])
  obtain ⟨ν, hν⟩ := exists_gen_negLB hG _ ρ.P 1 (baseOver (Sp S.R))
  have hact := ThetaCoord.isActOf_self hG ρ.P.isAb ρ.P.isLB (q := S.N) (b := 1)
    (by rw [ρ.N_eq]; exact ρ.n_odd.pow.pow) hν ρ.α_gen ρ.s_zero hm hN (ρ.U_sym a)
  have h₁ := ρ.U_act a ρ.i₀ _ hact
  have h₂ : ∀ j, (ρ.s ρ.i₀).f j = ∑ l, liftFun ρ.P.A _ (fn (algebraMap o S.R (if l = ρ.i₀ then 1 else 0))) *
      (ρ.s l).f j := fun j => by
    rw [Finset.sum_eq_single ρ.i₀ (fun b _ hb => by simp [hb, liftFun]) (by simp)]
    simp [liftFun]
  have h₃ := congrFun ((ρ.s_basis (ρ.s ρ.i₀)).unique h₁ h₂) l
  have h₄ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv).1 h₃
  exact hi (congrArg Subtype.val h₄)

end GlobalTheory.ThetaInvPart

namespace GlobalTheory

open ThetaInvPart

theorem proj_zero_pullback_ne_zero : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (S : ThetaSys o Ω) (ρ : S.Real) (k : Type) [Field k] (y : o →+* k) (T : AddSubgroup S.Gam), S.IsoFree T →
    ∃ j, y (S.proj T 0 j ρ.i₀) ≠ 0 := by
  intro hL o Ω _ _ _ hA S ρ k _ y T _
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : NeZero (ρ.n ^ ρ.k) := ⟨pow_ne_zero _ ρ.n_prime.ne_zero⟩
  have : IsDomain o := hA.inj.isDomain _
  have hd : ρ.n ^ ρ.k ∣ S.r * S.N := by
    rw [ρ.N_eq]; exact Dvd.dvd.mul_left (dvd_pow_self _ two_ne_zero) _
  let π : S.Gam →+ (Fin S.g ⊕ Fin S.g → ZMod (ρ.n ^ ρ.k)) :=
    (ZMod.castHom hd (ZMod (ρ.n ^ ρ.k))).toAddMonoidHom.compLeft _
  have hdiag := diag_eq π ρ.i₀ (by
      rw [ρ.card, ρ.N_eq, ← pow_mul]
      simp [two_mul])
    (fun a ha => rho_fix hL.1.globalFns hA.inj ρ a (funext fun i => by
      have h : ZMod.castHom hd (ZMod (ρ.n ^ ρ.k)) (a i) = 0 := congrFun ha i
      rw [← ZMod.natCast_zmod_val (a i), map_natCast, ZMod.natCast_eq_zero_iff] at h
      obtain ⟨c, hc⟩ := h
      rw [Pi.smul_apply, Pi.smul_apply, ← ZMod.natCast_zmod_val (a i), hc, nsmul_eq_mul, nsmul_eq_mul,
        ← Nat.cast_mul, ← Nat.cast_mul, Pi.zero_apply, ZMod.natCast_eq_zero_iff]
      exact ⟨c, by rw [ρ.N_eq]; ring⟩)) ρ.orbit
  have hu : ∀ n : ℕ, n ∣ Nat.card S.Gam → IsUnit (n : o) := fun n hn => by
    refine isUnit_of_dvd_unit (Nat.cast_dvd_cast hn) ?_
    rw [Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
    exact S.unit.pow _
  refine ⟨ρ.i₀, (IsUnit.map y ?_).ne_zero⟩
  have := Fintype.ofFinite T
  have hT := AddSubgroup.card_addSubgroup_dvd_card T
  have hK := (AddSubgroup.card_addSubgroup_dvd_card (π.comp T.subtype).ker).trans hT
  have hs : ∑ t : T, S.ρ t ρ.i₀ ρ.i₀ = (Nat.card (π.comp T.subtype).ker : o) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hdiag]
    by_cases h : π t = 0 <;> simp [AddMonoidHom.mem_ker, h]
  rw [ThetaSys.proj, finsum_eq_sum_of_fintype, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  simp only [AddMonoidHom.zero_apply, neg_zero, ZMod.val_zero, pow_zero, one_smul]
  rw [hs]
  exact (hu _ hT).ringInverse.mul (hu _ hK)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiEvenTauBimultDescendOfInjective
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section

namespace GlobalTheory.PullDescent

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem corr_of_val_genMap (hφ : Function.Injective φ) {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type}
    [Fintype K] [Fintype K'] {ψ : K → ((TK R).left ⟶ X)} {ε : K → ℤ} {ψ' : K' → ((TK R).left ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L ψ ε)} {t' : LB.Gen (LB.LinComb L ψ' ε')}
    (h : ∀ (z : (TK R').left) (J : ((TK R').left ⟶ X) → L.ι), Good L z J →
      val t (genMap hφ) z J = val t' (genMap hφ) z J) : LB.Gen.Corr L ψ ε ψ' ε' t t' :=
  corr_of_val_field_extension _ _ (fracMap hφ) X L hL K K' ψ ε ψ' ε' t t' h

theorem psiEven_desc (hG : GlobalFnsSt) (hφ : Function.Injective φ) (hD : IsPullDeg φ D D') (h : D'.PsiEven) :
    D.PsiEven := by
  intro χ
  obtain ⟨x, rfl⟩ := hD.xe.surjective χ
  refine corr_of_val_genMap hφ D.P.isLB fun z J hJ => ?_
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB (Z := (TK R').left) z
  have sq := fracMap_sq hφ
  have hh : (TK R').hom ≫ spMap φ = genMap hφ ≫ (TK R).hom := (Category.id_comp _).symm.trans sq
  have cW : (𝟙 _ ≫ D'.xK x) ≫ proj hD = genMap hφ ≫ D.xK (hD.xe x) := by
    rw [Category.id_comp]; exact cPoint_proj hD _ hh x
  have cn : D'.xK (-x) = D'.xK x ≫ (ι[D'.P.A]).left := by
    show (toUnit _ ≫ D'.c (-x)).left = _
    rw [PsiEvenPull.c_neg, ← Category.assoc, Over.comp_left]
  have c' : 𝟙 _ ≫ D'.xK (-x) = (𝟙 _ ≫ D'.xK x) ≫ (ι[D'.P.A]).left := by rw [cn, Category.assoc]
  have e := val_corr hJ' (h x) (𝟙 (TK R').left)
  rw [val_mul hJ', val_pull hJ'] at e
  have a₁ := psi_val hD (Z := (TK R').left) _ _ sq hJ hJ' (-x)
  have a₂ := psi_val hD (Z := (TK R').left) _ _ sq hJ hJ' x
  have a₃ : val D.sym (genMap hφ ≫ D.xK (hD.xe x)) z J =
      om hD.w z J J' ((𝟙 _ ≫ D'.xK x) ≫ (ι[D'.P.A]).left) * (om hD.w z J J' (𝟙 _ ≫ D'.xK x))⁻¹ *
        val D'.sym (𝟙 _ ≫ D'.xK x) z J' :=
    (congrArg (fun q => val D.sym q z J) cW.symm).trans (PsiEvenPull.sym_pull hG hD _ z hJ hJ')
  rw [c', map_neg] at a₁
  refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) a₁ ((val_pull hJ _ _ _).trans a₃))
    (Eq.trans ?_ a₂.symm))
  rw [← e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

set_option maxHeartbeats 1000000 in
theorem tauBimult_desc (hG : GlobalFnsSt) (hφ : Function.Injective φ) (hD : IsPullDeg φ D D') (h : D'.TauBimult) :
    D.TauBimult := by
  intro χ χ' ν
  obtain ⟨a, rfl⟩ := hD.xe.surjective χ
  obtain ⟨a', rfl⟩ := hD.xe.surjective χ'
  obtain ⟨b, rfl⟩ := hD.xe.surjective ν
  refine corr_of_val_genMap hφ D.P.isLB fun y J hJ => ?_
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB (Z := (TK R').left) y
  have sq := fracMap_sq hφ
  have hh : (TK R').hom ≫ spMap φ = genMap hφ ≫ (TK R).hom := (Category.id_comp _).symm.trans sq
  have gp := pull_grp hD
  let T : Over (Spec (CommRingCat.of R)) := Over.mk ((TK R').hom ≫ spMap φ)
  let κ : T ⟶ TK R := Over.homMk (genMap hφ) hh.symm
  let β : (TK R' ⟶ D'.P.A) → (T ⟶ D.P.A) := fun x => pushPt gp.1.w x
  have βc : ∀ χ, β (cP D' _ χ) = cP D _ (hD.xe χ) := fun χ => Over.OverMorphism.ext (by
    show ((TK R').hom ≫ (D'.c χ).left) ≫ proj hD = ((TK R').hom ≫ spMap φ) ≫ (D.c (hD.xe χ)).left
    rw [Category.assoc, hD.c_pr, Category.assoc])
  let Ω : (TK R' ⟶ D'.P.A) → ((TK R').left.presheaf.stalk y)ˣ := fun x => om hD.w (Z := (TK R').left) y J J' x.left
  let θ : (T ⟶ D.P.A) → (T ⟶ D.P.A) → (T ⟶ D.P.A) → ((TK R').left.presheaf.stalk y)ˣ := th D (T := T) y J
  have cub : ∀ a b c : TK R' ⟶ D'.P.A, θ (β a) (β b) (β c) =
        Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ *
          th D' (T := TK R') y J' a b c := by
    intro a b c
    have e := cub_pull hG hD (T' := TK R') hJ hJ' a b c
    have q : (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 = (lift (β a) (lift (β b) (β c))).left :=
      hom_ext_triple _ fun i => by
        rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
        fin_cases i <;> simp [x3] <;> rfl
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => om hD.w (Z := (TK R').left) y J J' q)) rfl)
  let τ : D.X → D.X → ((TK R').left.presheaf.stalk y)ˣ := fun a b => val (D.tau a b) (genMap hφ) y J
  let τ' : D'.X → D'.X → ((TK R').left.presheaf.stalk y)ˣ := fun a b => val (D'.tau a b) (𝟙 (TK R').left) y J'
  have vτ : ∀ a b, τ (hD.xe a) (hD.xe b) =
      (Ω (cP D' _ a * cP D' _ b))⁻¹ * Ω (cP D' _ a) * Ω (cP D' _ b) * (Ω 1)⁻¹ * τ' a b := fun a b => by
    have e := tau_val hD (Z := (TK R').left) _ _ sq hJ hJ' a b
    simp only [Category.id_comp] at e
    rw [← cPoint_add]
    exact e
  have e : τ' (a + a') b * th D' (T := TK R') y J' (cP D' _ a) (cP D' _ a') (cP D' _ b) = τ' a b * τ' a' b := by
    refine Eq.trans (congrArg₂ (· * ·) rfl ?_)
      ((val_mul hJ' _ _ _).symm.trans ((val_corr hJ' (h a a' b) (𝟙 (TK R').left)).trans (val_mul hJ' _ _ _)))
    refine Eq.trans ?_ (val_cub D'.cub (𝟙 (TK R')) hJ' (cP D' _ a) (cP D' _ a') (cP D' _ b)).symm
    rw [Category.id_comp, Category.id_comp, Category.id_comp]
  have key : τ (hD.xe a + hD.xe a') (hD.xe b) * θ (cP D T (hD.xe a)) (cP D T (hD.xe a')) (cP D T (hD.xe b)) =
      τ (hD.xe a) (hD.xe b) * τ (hD.xe a') (hD.xe b) := by
    rw [← βc, ← βc, ← βc, cub, ← map_add (f := _), vτ, vτ, vτ, cPoint_add]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) key
  refine (val_cub D.cub κ hJ (cP D _ (hD.xe a)) (cP D _ (hD.xe a')) (cP D _ (hD.xe b))).trans ?_
  rw [comp_cP, comp_cP, comp_cP]

end GlobalTheory.PullDescent

namespace GlobalTheory

theorem psiEven_tauBimult_of_isPullDeg_injective : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R'), Function.Injective φ → ∀ (D : DegPre R) (D' : DegPre R') (_ : IsPullDeg φ D D'), (D'.PsiEven → D.PsiEven) ∧ (D'.TauBimult → D.TauBimult) :=
  fun hG _ _ _ _ _ _ _ hφ _ _ hD => ⟨PullDescent.psiEven_desc hG hφ hD, PullDescent.tauBimult_desc hG hφ hD⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiRelationDescendsFieldExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiRelationDescent

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)

def chartPullComb {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) :
    ChartPull ((LB.LinComb L φ ε).pull h) (LB.LinComb L (fun k => h ≫ φ k) ε) (𝟙 Y') :=
  have le : ∀ J : PUnit → K → L.ι, ((LB.LinComb L φ ε).pull h).U J ≤
      LB.wchart L (fun k => h ≫ φ k) (J PUnit.unit) :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem_pull.1 hy) k
  { idx := fun J => J PUnit.unit
    le := le
    g := fun y J J' hj hj' => by
      refine (gm_pull_g (LB.LinComb L φ ε) h (𝟙 Y') y J J' hj hj').trans
        ((gm_linComb L φ ε (𝟙 Y' ≫ h) y _ _ (mem_pull.1 hj) (mem_pull.1 hj')).trans
          (Eq.trans ?_ (gm_linComb L (fun k => h ≫ φ k) ε (𝟙 Y') y _ _ (le J hj) (le J' hj')).symm))
      simp only [Category.assoc] }

section

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]
  (oa : D.OAct O) (w : O)

abbrev mor : Fin 4 → (D.P.A.left ⟶ D.P.A.left) :=
  ![(padd D.P.A (𝟙 _) (oa.onB.act w)).left, 𝟙 D.P.A.left, (oa.onB.act w).left, (toUnit D.P.A ≫ η[D.P.A]).left]

theorem prod_mor {T : Over (Sp R)} (x : T ⟶ D.P.A) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k : Fin 4, h (x.left ≫ mor oa w k) ^ (![1, -2, -1, 2] : Fin 4 → ℤ) k =
      h (x * (x ≫ oa.onB.act w)).left * (h x.left ^ 2)⁻¹ * (h (x ≫ oa.onB.act w).left)⁻¹ *
        h (1 : T ⟶ D.P.A).left ^ 2 := by
  have a₀ : x ≫ padd D.P.A (𝟙 _) (oa.onB.act w) = x * (x ≫ oa.onB.act w) :=
    (MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id])
  have a₁ : x ≫ toUnit D.P.A ≫ η[D.P.A] = 1 := MonObj.comp_one (M := D.P.A) x
  rw [Fin.prod_univ_four]
  show h (x ≫ padd D.P.A (𝟙 _) (oa.onB.act w)).left ^ (1 : ℤ) * h (x.left ≫ 𝟙 _) ^ (-2 : ℤ) *
    h (x ≫ oa.onB.act w).left ^ (-1 : ℤ) * h (x ≫ toUnit D.P.A ≫ η[D.P.A]).left ^ (2 : ℤ) = _
  rw [a₀, a₁, Category.comp_id]
  simp only [zpow_neg, zpow_ofNat, pow_one]

theorem prod_mor_one {T : Over (Sp R)} {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k : Fin 4, h ((1 : T ⟶ D.P.A).left ≫ mor oa w k) ^ (![1, -2, -1, 2] : Fin 4 → ℤ) k = 1 := by
  have := oa.onB.hom w
  rw [prod_mor, MonObj.one_comp, _root_.mul_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one]
  abel

theorem exists_normalised (u : LB.Gen (LB.LinComb D.P.L (mor oa w) ![1, -2, -1, 2])) (hu : u.IsGen) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (mor oa w) ![1, -2, -1, 2]), t.IsGen ∧
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t (eSec D.P.A)) (LB.oneGen D.P.L) := by
  obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB (φ' := mor oa w) (ε' := ![1, -2, -1, 2])
    (fun V _ k => by
      refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _
        (c := ∏ i, k (mor oa w i) ^ (![1, -2, -1, 2] : Fin 4 → ℤ) i) rfl
        (prod_neg _ _ (prod_mor_one oa w (T := D.P.A) k))) ?_
      simp)
    (LB.mulGen D.P.L _ _ _ _ u (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ u (1 : D.P.A ⟶ D.P.A).left)))
    (mulGen_isGen _ _ _ _ _ _ _ hu (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hu _)))
  refine ⟨t, ht, corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have e : eSec D.P.A ≫ (1 : D.P.A ⟶ D.P.A).left = eSec D.P.A :=
    (congrArg (fun q => q.left) (MonObj.comp_one (M := D.P.A) η[D.P.A])).trans (Category.id_comp _)
  rw [val_pull hJ, val_one, Category.id_comp, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, e, mul_inv_cancel]

end

end GlobalTheory.PsiRelationDescent

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcPull GlobalTheory.PsiRelationDescent in
theorem psi_relation_descend_field : GlobalFnsSt → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K₀) (D' : DegPre K) (hD : IsPullDeg i D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] (oa : D.OAct O) (oa' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (oa'.onB.act a).left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ (oa.onB.act a).left) → ∀ w : O, TraceFormTwistIso D' oa' w → TraceFormTwistIso D oa w := by
  intro hG K₀ K _ _ i D D' hD O _ _ _ _ oa oa' hx ho w ⟨u', hu', u₀', hy'⟩
  have gp := pull_grp hD
  have hφ : Function.Injective i := i.injective
  have i₁ : (𝟙 D'.P.A : D'.P.A ⟶ _).left ≫ PsiEvenPull.proj hD =
      PsiEvenPull.proj hD ≫ (𝟙 D.P.A : D.P.A ⟶ _).left :=
    (Category.id_comp _).trans (Category.comp_id _).symm
  have i₂ : (toUnit D'.P.A ≫ η[D'.P.A]).left ≫ PsiEvenPull.proj hD =
      PsiEvenPull.proj hD ≫ (toUnit D.P.A ≫ η[D.P.A]).left := by
    show (D'.P.A.hom ≫ eSec D'.P.A) ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ D.P.A.hom ≫ eSec D.P.A
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hD.he).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) gp.1.w.symm).trans (Category.assoc _ _ _))))
  have hψ : ∀ k, mor oa' w k ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ mor oa w k := fun k => by
    fin_cases k
    exacts [mul_push gp _ i₁ (ho w), i₁, ho w, i₂]
  obtain ⟨s, hs, -⟩ := exists_up_om ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB (mor oa' w)
    (fun k => PsiEvenPull.proj hD ≫ mor oa w k) _ hψ u' hu'
  obtain ⟨u₁, hu₁⟩ := (lb_gen_iso_descend_field K₀ K i _ _ D.P.A.hom D'.P.A.hom (PsiEvenPull.proj hD)
    D.P.isAb.smooth D.P.isAb.proper D.P.isAb.geomConnected gp.1).1 (LB.LinComb D.P.L (mor oa w) ![1, -2, -1, 2])
    (LB.isLB_linComb D.P.isLB _ _) ⟨_, GtBaseChange.genPull_isGen (chartPullComb D.P.L (mor oa w) _ _) hs⟩
  obtain ⟨u, hu, u₀⟩ := exists_normalised oa w u₁ hu₁
  obtain ⟨t, ht, vt⟩ := exists_down_om hD.w_gen D.P.isLB D'.P.isLB (φ' := mor oa' w) (PsiEvenPull.proj hD) hψ u hu
  have tu := gen_unique D'.P.isLB D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2 ht hu'
    fun y J' hJ' => by
      obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
      have o₁ : (1 : 𝟙_ (Over (Sp K)) ⟶ D'.P.A).left = eSec D'.P.A := Category.id_comp _
      have e := vt _ (1 : 𝟙_ (Over (Sp K)) ⟶ D'.P.A).left y J J' hJ hJ'
      rw [prod_mor_one, _root_.one_mul, o₁, hD.he] at e
      have e₁ := (val_pull hJ _ _ _).symm.trans ((val_corr hJ u₀ (specOf i)).trans (val_one _))
      have e₂ := (val_pull hJ' _ _ _).symm.trans ((val_corr hJ' u₀' (𝟙 _)).trans (val_one _))
      rw [Category.id_comp] at e₂
      exact e.symm.trans (e₁.trans e₂.symm)
  refine ⟨u, hu, u₀, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hD.xe.surjective y
  refine corr_of_val_field_extension _ _ (fracMap hφ) _ _ D.P.isLB _ _ _ _ _ _ _ _ fun z J hJ => ?_
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB (Z := (TK K).left) z
  have sq := fracMap_sq hφ
  have hh : (TK K).hom ≫ spMap i = genMap hφ ≫ (TK K₀).hom := (Category.id_comp _).symm.trans sq
  have e := val_corr hJ' (hy' x) (𝟙 _)
  have v := vt _ (cP D' (TK K) x).left z J J' hJ hJ'
  rw [prod_mor, cPoint_proj hD _ hh, ← TorusExt.cPoint_smul oa', ← cPoint_add, tu _ _ z J' hJ'] at v
  have c₀ : ∀ x, (cP D' (TK K) x).left = D'.xK x := fun _ => rfl
  have c₁ : ∀ x, (cP D (TK K₀) x).left = D.xK x := fun _ => rfl
  simp only [c₀, c₁] at v
  rw [val_mul hJ', val_mul hJ', val_pull hJ', Category.id_comp] at e
  show val (LB.mulGen D.P.L _ _ _ _ (D.tau (hD.xe x) (w • hD.xe x)) (LB.pullGen D.P.L _ _ u (D.xK (hD.xe x))))
    (genMap hφ) z J = val (LB.mulGen D.P.L _ _ _ _ (D.psi (hD.xe x)) D.rigK) (genMap hφ) z J
  have hJ₀ : Good (Z := (TK K).left) D.P.L z J := hJ
  rw [val_mul hJ₀, val_mul hJ₀, val_pull hJ₀, v, ← hx, tau_val hD _ _ sq hJ₀ hJ', psi_val hD _ _ sq hJ₀ hJ',
    rig_val hD _ _ sq hJ₀ hJ']
  simp only [Category.id_comp]
  have e' := congrArg Additive.ofMul e
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at e' ⊢
  linear_combination (norm := abel) e'

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiScalarEqExpansionCoefRatio
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiRatio

theorem exists_cstHom {F : Type} [CommRing F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) :
    ∃ φ : F →+* Z.presheaf.stalk z, (∀ c, cst p z c = φ c) ∧ ∀ c, gs (𝟙 _) z ⊤ (scal p c) = φ c := by
  refine ⟨(Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp ((p.app ⊤).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom), fun c => gs_eq p z ⊤ trivial _, fun c => ?_⟩
  exact gs_eq (𝟙 _) z ⊤ trivial _

theorem cst_eq_scal {F : Type} [CommRing F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (c : F) :
    cst p z c = gs (𝟙 _) z ⊤ (scal p c) := by
  obtain ⟨φ, h₁, h₂⟩ := exists_cstHom p z
  rw [h₁, h₂]

end GlobalTheory.PsiRatio

namespace GlobalTheory

theorem psiScal_eq_ratio : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (th : SecBT D (𝟙_ _) 1 0), PsiScal D ga a → PsiRel D (𝟙_ _) f → FibNZ (𝟙_ _ ⊗ D.P.A).hom th → ∀ (χ : D.X) (q p : R), Mult D th (f 0) q → Coef D χ (ga χ) th (f χ) p → algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) p := by
  intro R _ _ D ga a f th hS hR hN χ q p hq hp
  let B : Over (Spec (CommRingCat.of R)) := 𝟙_ _ ⊗ D.P.A
  let T : Over (Spec (CommRingCat.of R)) := TK R ⊗ B
  let pt : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
  obtain ⟨z₀, hz₀, hth⟩ := hN (jK R pt)
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := jK R) (g := B.hom) pt z₀ hz₀.symm
  let z' : T.left := z
  obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z'
  let x : T ⟶ D.P.A := snd (TK R) B ≫ snd _ _
  have ex : lift (toUnit T) x = snd (TK R) B := by
    ext1
    · exact toUnit_unique _ _
    · exact lift_snd _ _
  have ey : x * (cT D T χ)⁻¹ * cT D T χ = x := inv_mul_cancel_right _ _
  have hu : IsUnit (sval th (snd (TK R) B).left z' J) := by
    refine (MulPullSec.mem_nonzeroLocus_iff th (snd (TK R) B).left z' hJ).1 ?_
    have : (snd (TK R) B).left z' = z₀ := hz
    rw [this]
    exact hth
  have e₁ := hR χ T (toUnit _) (fst (TK R) B) (x * (cT D T χ)⁻¹) z' J hJ
  have e₂ := (hS χ).2 T (fst (TK R) B) z' J hJ
  have e₃ := hq _ (snd (TK R) B).left z' J hJ
  have e₄ := hp T (x * (cT D T χ)⁻¹) z' J hJ
  rw [ey, ex] at e₁ e₄
  have e' : T.hom = (fst (TK R) B).left ≫ jK R := (Over.w (fst (TK R) B)).symm
  have e'' : (snd (TK R) B).left ≫ B.hom = (fst (TK R) B).left ≫ jK R := (Over.w (snd (TK R) B)).trans e'
  obtain ⟨φ, -, hφ⟩ := PsiRatio.exists_cstHom (F := FractionRing R) (fst (TK R) B).left z'
  have hc : ∀ c : R, cst ((fst (TK R) B).left ≫ jK R) z' c = φ (algebraMap R (FractionRing R) c) := fun c =>
    (PsiRatio.cst_eq_scal _ _ _).trans ((congrArg (gs (𝟙 _) z' ⊤) (PsiInt.scal_jK _ c)).trans (hφ _))
  have c₃ := (congrArg (fun s => cst s z' q) e'').trans (hc q)
  have c₄ := (congrArg (fun s => cst s z' p) e').trans (hc p)
  have alg : ∀ (A : Type) [CommRing A] (s s₀ t cq cp ca cq' cp' ca' : A) (u g r : Aˣ), IsUnit t →
      s = (u * r).val * s₀ → u.val = ca * g.val → s₀ = cq * t → s = cp * ((g * r).val * t) →
      cq = cq' → cp = cp' → ca = ca' → cq' * ca' = cp' := by
    intro A _ s s₀ t cq cp ca cq' cp' ca' u g r ht h₁ h₂ h₃ h₄ h₅ h₆ h₇
    subst h₅ h₆ h₇
    refine (((g * r).isUnit.mul ht).mul_left_inj).1 ?_
    rw [← h₄, h₁, h₃, Units.val_mul, Units.val_mul, h₂]
    ring
  apply φ.injective
  rw [map_mul]
  exact alg _ _ _ _ _ _ _ _ _ _ _ _ _ hu e₁ e₂ e₃ e₄ c₃ c₄ (hφ _)

end GlobalTheory
end

