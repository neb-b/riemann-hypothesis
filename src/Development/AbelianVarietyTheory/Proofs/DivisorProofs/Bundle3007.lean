module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2975
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1984
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorsDifferenceGlobal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2998
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2977
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2980
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2963

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberTorsionSectionLiesOverSecondMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UCanon

theorem torsion_sec_over_second : ∀ (k : Type) [Field k] {S : Scheme.{0}} (G' : Over (Sp (DualNumber k))) [GrpObj G'], IsAbelianScheme G' → ∀ (G : Over S) [GrpObj G] (g₁ g₂ : Sp (DualNumber k) ⟶ S) (φ₁ φ₂ : G'.left ⟶ G.left), IsGrpPullback G' G g₂ φ₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ G'.left) (y : Z ⟶ Sp k), x ≫ G'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ φ₁ = x ≫ φ₂) → spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₁ = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₂ → ∀ (n : ℕ), (n : k) ≠ 0 → ∀ (σ : 𝟙_ (Over S) ⟶ G), σ ^ n = 1 → ∀ (x : 𝟙_ (Over (Sp (DualNumber k))) ⟶ G'), x ^ n = 1 → x.left ≫ φ₁ = g₁ ≫ σ.left → x.left ≫ φ₂ = g₂ ≫ σ.left := by
  intro k _ S G' _ hab G _ g₁ g₂ φ₁ φ₂ h₂ h0 hg n hn σ hσ x hx hx₁
  let T := 𝟙_ (Over (Sp (DualNumber k)))
  have hsq : ∀ y : T ⟶ G', (y.left ≫ φ₂) ≫ G.hom = T.hom ≫ g₂ := by
    intro y
    rw [Category.assoc, h₂.1.w, ← Category.assoc, Over.w y]
  let ψ : (T ⟶ G') → (Over.mk (T.hom ≫ g₂) ⟶ G) := fun y => Over.homMk (y.left ≫ φ₂) (hsq y)
  have ψmul : ∀ a b, ψ (a * b) = ψ a * ψ b := by
    intro a b
    apply Over.OverMorphism.ext
    exact (h₂.2 T a b (ψ a) (ψ b) rfl rfl).symm
  let Ψ : (T ⟶ G') →* (Over.mk (T.hom ≫ g₂) ⟶ G) := MonoidHom.mk' ψ ψmul
  have Ψinj : ∀ a b : T ⟶ G', Ψ a = Ψ b → a = b := by
    intro a b hab'
    apply Over.OverMorphism.ext
    exact h₂.1.hom_ext (congrArg CommaMorphism.left hab') (by rw [Over.w a, Over.w b])
  have hw : (g₂ ≫ σ.left) ≫ G.hom = 𝟙 (Sp (DualNumber k)) ≫ g₂ := by
    rw [Category.assoc, Over.w σ]; simp
  let x' : T ⟶ G' := Over.homMk (h₂.1.lift (g₂ ≫ σ.left) (𝟙 _) hw) (by simp [T])
  have hx'φ : x'.left ≫ φ₂ = g₂ ≫ σ.left := h₂.1.lift_fst _ _ _
  let u : Over.mk (T.hom ≫ g₂) ⟶ 𝟙_ (Over S) := toUnit _
  have hu : u.left = g₂ := by
    have := Over.w u
    simpa [T] using this
  have hΨx' : Ψ x' = u ≫ σ := by
    apply Over.OverMorphism.ext
    show x'.left ≫ φ₂ = u.left ≫ σ.left
    rw [hx'φ, hu]
  have hpow : ∀ m : ℕ, u ≫ σ ^ m = (u ≫ σ) ^ m := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
    | succ m ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
  have hx'n : x' ^ n = 1 := by
    apply Ψinj
    rw [map_pow, map_one, hΨx', ← hpow, hσ, MonObj.comp_one]
  have hb : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x.left =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x'.left := by
    apply h₂.1.hom_ext
    · have h1 := h0 (Sp k) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x.left) (𝟙 _)
        (by rw [Category.assoc, Over.w x]; simp [T])
      rw [← h1, Category.assoc, Category.assoc, hx₁, ← Category.assoc, hg, Category.assoc, hx'φ]
    · rw [Category.assoc, Category.assoc, Over.w x, Over.w x']
  have key := _root_.GlobalTheory.UCanon.eq_of_pow_eq_of_eq_at_closed k G' hab n hn x x' (by rw [hx, hx'n]) hb
  rw [key]
  exact hx'φ

end GlobalTheory.UCanon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerDegDataLatticeIsoEquivariant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

theorem GlobalTheory.Poinc.Sep.sharpRef_equivariant_of_unif_pow : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → (∀ a, (c.lev a).left ≫ φc = y ≫ (F.univ.lev a).left) → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∃ e : (Fin 8 → Q.X) ≃+ D.toPre.X, SharpRef W Q ρ D.toPre e ∧ ∀ a a' : Matrix (Fin 8) (Fin 8) ℤ, (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ E : EndU U.toUnifPre, (∀ u, E.aG ≫ q u = (List.ofFn fun v => q v ^ a u v).prod) → ∀ mu, E.h (e mu) = e fun u => ∑ v, a' u v • mu v := by
  intro g n o _ ζ F W hW V _ _ _ Q V₁ _ _ _ ρ hCN hinj hfin D₀ e₀ hR G₀ _ _ A₀ U₀ y α α₂ hsa hpb hsq hlb P cS φc φ₂ hpbc hsqc hlbc hlev pr hpr hpru hPL G _ _ hG D U q hq hqu hqc
  obtain ⟨ch, hch, hbij⟩ := _root_.GlobalTheory.Poinc.Eq8.Chars8.main V₁ hCN D₀ A₀ G₀ hsa U₀ D P G hG U q hq hqu
  let act : Matrix (Fin 8) (Fin 8) ℤ → (Fin 8 → Q.X) → (Fin 8 → Q.X) := fun N mu u => ∑ v, N u v • mu v
  have hact : ∀ N N' mu, act N (act N' mu) = act (N * N') mu := by
    intro N N' mu
    funext u
    simp only [act, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm
  have hone : ∀ mu, act 1 mu = mu := by
    intro mu
    funext u
    simp [act, Matrix.one_apply]
  have hdet : IsUnit (W + W.transpose).det := by rw [hW.2]; exact isUnit_one
  have hM1 : (W + W.transpose) * (W + W.transpose)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hM2 : (W + W.transpose)⁻¹ * (W + W.transpose) = 1 := Matrix.nonsing_inv_mul _ hdet
  have hactadd : ∀ N mu mu', act N (mu + mu') = act N mu + act N mu' := by
    intro N mu mu'
    funext u
    simp [act, smul_add, Finset.sum_add_distrib]
  let f : (Fin 8 → Q.X) →+ D.toPre.X :=
    { toFun := fun mu => ∑ u, ch u (e₀.symm (act (W + W.transpose) mu u))
      map_zero' := by
        have : act (W + W.transpose) 0 = 0 := by funext u; simp [act]
        simp [this]
      map_add' := by
        intro mu mu'
        simp only [hactadd, Pi.add_apply, map_add (f := _), Finset.sum_add_distrib] }
  have hfb : Function.Bijective f := by
    have hA : Function.Bijective (act (W + W.transpose)) := by
      refine ⟨fun x y hxy => ?_, fun x => ⟨act (W + W.transpose)⁻¹ x, by rw [hact, hM1, hone]⟩⟩
      have := congrArg (act (W + W.transpose)⁻¹) hxy
      rwa [hact, hact, hM2, hone, hone] at this
    have hE : Function.Bijective (fun x : Fin 8 → Q.X => fun u => e₀.symm (x u)) := by
      refine ⟨fun x y hxy => ?_, fun x => ⟨fun u => e₀ (x u), by funext u; simp⟩⟩
      funext u
      exact e₀.symm.injective (congrFun hxy u)
    exact hbij.comp (hE.comp hA)
  let e : (Fin 8 → Q.X) ≃+ D.toPre.X := AddEquiv.ofBijective f hfb
  refine ⟨e, GlobalTheory.T.degenerationData_eighthPower_via_characterMaps g n o ζ F W hW V Q V₁ ρ hCN hinj hfin D₀ e₀ hR G₀ A₀ U₀ y α α₂ hsa hpb hsq hlb P cS φc φ₂ hpbc hsqc hlbc hlev pr hpr hpru hPL G hG D U q hq hqu hqc ch hch e (fun mu => rfl), ?_⟩
  intro a a' hM E hE mu
  have hEc := _root_.GlobalTheory.Poinc.Eq8.endChar_endU V₁ hCN D P G hG U E
  have key := _root_.GlobalTheory.Poinc.MatChar.charMap_matrix V₁ hCN D₀ A₀ G₀ hsa U₀ D P G hG U q hq ch hch a E.aG E.h E.homG hEc hE
  show E.h (f mu) = f (act a' mu)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum, key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_zsmul, ← map_sum]
  congr 2
  have h3 : act (W + W.transpose) (act a' mu) = act a.transpose (act (W + W.transpose) mu) := by
    rw [hact, hact, hM]
  rw [h3]
  simp [act, Matrix.transpose_apply]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSelfOfConeCongMod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.eq_self_of_cone_congMod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)) (q : ℕ), IsPolFan H.bar q φ → NoSelfInt H.bar q φ → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Finite (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ δ → (∀ y, y ≠ 0 → 0 < ∑ i, δ i y y) → ∀ (u : X ≃ₗ[𝓞 E] X) (a a' : Fin m → ℕ), (∀ i, 0 < a i) → (∀ i, 0 < a' i) → (∀ y z, ∑ i, (a i : ℤ) * δ i (u y) (u z) = ∑ i, (a' i : ℤ) * δ i y z) → ∀ N : ℕ, 3 ≤ N → (∀ y, ∃ z, u y = y + N • z) → ∀ y, u y = y := by
  intro E _ _ _ H φ q hfan hno X _ _ _ _ _ hX m δ hδ hdef u a a' ha ha' hsum N hN hcong
  haveI : Module.Projective (𝓞 E) X := GlobalTheory.Forms.projective_of_int (𝓞 E) X
  have hon : IsPolFanOn H.bar φ X := hfan X hX
  have hu : IsCone H.bar φ fun i => pull u.toLinearMap (δ i) := hδ.pull_equiv u
  have heq : ∑ j, a j • pull u.toLinearMap (δ j) = ∑ j, a' j • δ j := LinearMap.ext₂ fun y z => by
    simpa [LinearMap.sum_apply, nsmul_eq_mul] using hsum y z
  have hfix : ∀ j, pull u.toLinearMap (δ j) = δ j := by
    intro j
    obtain ⟨j', hj'⟩ := GlobalTheory.Poinc.intCone_face (𝓞 E) H.bar φ X hon _ _ _ δ hu hδ a a' ha heq j
    obtain rfl := hno X hX m δ hδ u j j' hj'
    exact hj'
  have hβ : ∀ y z, (∑ i, δ i) (u y) (u z) = (∑ i, δ i) y z := fun y z => by
    simp only [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => LinearMap.congr_fun₂ (hfix i) y z
  have he := GlobalTheory.Poinc.eq_refl_of_isometry_congMod X (∑ i, δ i)
    (fun y hy => by simpa [LinearMap.sum_apply] using hdef y hy) (u.restrictScalars ℤ) (fun y z => hβ y z) N hN
    (fun y => hcong y)
  intro y
  exact LinearEquiv.congr_fun he y
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyIndEtaleBaseChangeStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_cohomology_ind_etale_base_change : GlobalTheory.EtC.C3 := by
  first | (exact @GlobalTheory.EtC.LineAcyc.c3) | (exact GlobalTheory.EtC.LineAcyc.c3) | (intros; apply GlobalTheory.EtC.LineAcyc.c3  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineScalarTorusInvariantHeatOperators
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatUniq

theorem exists_affine_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h h' : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → IsBasic Y h' → h.Θ = h'.Θ → h.u = h'.u → ∃ (ℓ : Q.X →+ R) (π π' : R), ∀ (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α), TActs Y h k α σ σ' → TActs Y h' k α σ σ'' → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ'' x.left z J = sval σ' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom (2 * (k : R) * ℓ α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π')) * sval σ x.left z J := by
  intro R _ _ _ _ _ Q O _ _ _ oa Y n v dd hdd D h' h hb' hb hΘ' hu'
  have hΘ : h.Θ = h'.Θ := hΘ'.symm
  have hu : h.u = h'.u := hu'.symm
  obtain ⟨e, π, π', hT, hG⟩ := _root_.GlobalTheory.HeatUniqGlob.main R Q O oa Y n v dd hdd D h h' hb hb' hΘ hu
  obtain ⟨ℓ, hℓ⟩ := _root_.GlobalTheory.HeatMod.TorUniq.exists_addHom_of_kills_wt_zero R Q O oa Y n v dd hdd e hT
  refine ⟨ℓ, π, π', ?_⟩
  intro k α σ σ'' σ' h1' h1 T x z J hJ
  refine _root_.GlobalTheory.Heat.sval_eq_of_localIdentity R Q O oa Y n v dd hdd D h h' hb hb'
    (fun k α => 2 * (k : R) * ℓ α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π') ?_ k α σ σ' σ'' h1 h1' T x z J hJ
  intro i i' k α V hV f hf
  obtain ⟨h2d, h3, h4⟩ := hG i i' _ hV
  simp only [dlg] at h2d h3 h4
  have hle : Y.q.left ⁻¹ᵁ V ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j i) ⊓ Q.P.L.U (h'.j i')) := fun pt hpt =>
    ⟨h.le i (hV hpt).1, h'.le i' (hV hpt).2⟩
  have hg : pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) *
      pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i'))⁻¹.val (Y.q.left ⁻¹ᵁ V) = 1 := by
    unfold pbT
    rw [dite_eq_left hle, dite_eq_left hle, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have mono : ∀ (δ : Fld Y.H.left) {W₁ W₂ : Y.H.left.Opens}, W₁ ≤ W₂ → IsField W₂ δ → IsField W₁ δ :=
    fun δ W₁ W₂ hle H => ⟨fun W hW => H.1 W (hW.trans hle), fun W hW => H.2.1 W (hW.trans hle),
      fun W W' hh hW => H.2.2 W W' hh (hW.trans hle)⟩
  rw [_root_.GlobalTheory.HeatConj.op_pow_mul R Y.H n dd h.Θ h.symm h.u (h.d i) (h.W i) (h.W i) _ (h.p i) (h.p' i) k _ _ hg (hV.trans inf_le_left)
    (h.lift i).1 (fun a => mono _ le_top (hdd a).1) f]
  congr 1
  have hc : constFn Y.H.hom (Y.q.left ⁻¹ᵁ V) (2 * (k : R) * ℓ α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π') =
      2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) * constFn Y.H.hom _ (ℓ α) +
        2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) ^ 2 * constFn Y.H.hom _ π +
        2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) * constFn Y.H.hom _ π' := by
    simp only [constFn, map_add (f := _), map_mul, map_pow, map_natCast, map_ofNat]
  simp only [hc]
  have hl := hℓ α V f hf
  unfold op
  rw [← hΘ, ← hu]
  linear_combination (2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V))) * h2d f + (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) ^ 2 * f * h3 +
    (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) * f * h4 + 2 * (k : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)) * hl

end GlobalTheory.HeatUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseSchOfHomScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.BaseSch

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_injective {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g := by
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  simpa using this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem lowMap_eq {l : Geo.Tor.Level H} (c : Coeff l) {A : Type} [CommRing A] (b : c.F →+* A) :
    lowMap c b = spMap b ≫ lowMap c (RingHom.id c.F) := by
  simp only [lowMap, RingHom.id_comp]
  rw [← spMap_comp']

theorem objMap_congr {D : Datum H} {l : Geo.Tor.Level H} {S S' : Scheme.{0}} {s : S ⟶ Sp (KA l)}
    {s' : S' ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s} {o' : Obj D l (baseKA l) s'} {f f' : S' ⟶ S} (h : f = f')
    (m : ObjMap o' o f) : ∃ m' : ObjMap o' o f', m'.toSABMap.φ = m.toSABMap.φ := by
  subst h
  exact ⟨m, rfl⟩

theorem exists_section_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {q : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G q φ) (σ : 𝟙_ (Over S) ⟶ G) :
    ∃ σ' : 𝟙_ (Over S') ⟶ G', σ'.left ≫ φ = q ≫ σ.left := by
  have hw : (q ≫ σ.left) ≫ G.hom = 𝟙 S' ≫ q := by
    rw [Category.assoc, Over.w σ]
    simp
  refine ⟨Over.homMk (h.1.lift (q ≫ σ.left) (𝟙 S') hw) (by simpa using h.1.lift_snd _ _ hw), ?_⟩
  simp

theorem hom_ext_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {q : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G q φ) {T : Over S'} (σ₁ σ₂ : T ⟶ G')
    (e : σ₁.left ≫ φ = σ₂.left ≫ φ) : σ₁ = σ₂ := by
  ext1
  exact h.1.hom_ext e (by rw [Over.w σ₁, Over.w σ₂])

theorem pull_mul {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {q : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G q φ) (σ₁ σ₂ : 𝟙_ (Over S') ⟶ G') (τ₁ τ₂ : 𝟙_ (Over S) ⟶ G)
    (h₁ : σ₁.left ≫ φ = q ≫ τ₁.left) (h₂ : σ₂.left ≫ φ = q ≫ τ₂.left) :
    (σ₁ * σ₂).left ≫ φ = q ≫ (τ₁ * τ₂).left := by
  let Q : Over.mk ((𝟙_ (Over S')).hom ≫ q) ⟶ 𝟙_ (Over S) := Over.homMk q (by simp)
  have e := h.2 (𝟙_ (Over S')) σ₁ σ₂ (Q ≫ τ₁) (Q ≫ τ₂) (by simp [Q, h₁]) (by simp [Q, h₂])
  rw [← e, ← MonObj.comp_mul]
  simp [Q]

theorem sec_comp_eq {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} (f : S' ⟶ S) (φ : G'.left ⟶ G.left)
    (hw : φ ≫ G.hom = G'.hom ≫ f) (σ : 𝟙_ (Over S') ⟶ G') (τ : 𝟙_ (Over S) ⟶ G) :
    (σ.left ≫ φ) ≫ G.hom = (f ≫ τ.left) ≫ G.hom := by
  rw [Category.assoc, hw, Category.assoc, Over.w τ, ← Category.assoc, Over.w σ]
  simp

end GlobalTheory.UCanon.BaseSch

namespace GlobalTheory.UCanon.BaseSch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}


set_option maxHeartbeats 800000 in
theorem of_homScheme (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    (Cs : Scheme.{0}) (g : Cs ⟶ Sp c.F)
    (oC : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) (g ≫ lowMap c (RingHom.id c.F)))
    (u : X → (𝟙_ (Over Cs) ⟶ oC.t.G)) (N : ℕ) (hsm : SmoothOfRelativeDimension N g)
    (hex : ∀ (V : Type) [CommRing V] [IsReduced V] (bV : c.F →+* V) (o' : LowObj D' c bV)
      (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) →
      (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (v : Sp V ⟶ Cs) (m : ObjMap o' oC v),
        v ≫ g = spMap bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ = v ≫ (u y).left)
    (huniq : ∀ (A : Type) [CommRing A] [IsReduced A] (v₁ v₂ : Sp A ⟶ Cs), v₁ ≫ g = v₂ ≫ g →
      ∀ (s' : Sp A ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s')
        (m₁ : ObjMap o'' oC v₁) (m₂ : ObjMap o'' oC v₂) (z : X → (Sp A ⟶ o''.t.G.left)),
        s' = v₁ ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v₁ ≫ (u y).left) →
        (∀ y, z y ≫ m₂.toSABMap.φ = v₂ ≫ (u y).left) → v₁ = v₂)
    (heps : ∀ (k : Type) [Field k] (v : Sp (DualNumber k) ⟶ Cs) (s' : Sp (DualNumber k) ⟶ Sp (KA (LowDat.lowLevel l)))
      (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v)
      (m₂ : ObjMap o'' oC (constPt v)) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)),
      s' = v ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v ≫ (u y).left) →
      (∀ y, z y ≫ m₂.toSABMap.φ = constPt v ≫ (u y).left) → v = constPt v)
    (hadd : ∀ y z, u (y + z) = u y * u z) (hlin : ∀ (a : 𝓞 E) y, u (a • y) = u y ≫ oC.t.act.act a)
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (bV : c.F →+* V) (o' : LowObj D' c bV)
    (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)) (hx : ∀ y z, x (y + z) = x y * x z)
    (hxl : ∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsRegularLocalRing W) (b : c.F →+* W) (o : LowObj D' c b)
      (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ o.t.G)) (θ₀ : W →+* V) (m : ObjMap o' o (spMap θ₀)),
      b.EssFiniteType ∧ (∀ y z, x₀ (y + z) = x₀ y * x₀ z) ∧ (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ o.t.act.act a) ∧
      IsLocalHom θ₀ ∧ θ₀.comp b = bV ∧ (∀ y, (x y).left ≫ m.toSABMap.φ = spMap θ₀ ≫ (x₀ y).left) ∧
      ((∀ (A : Type) [CommRing A] [IsReduced A] (f₁ f₂ : W →+* A), f₁.comp b = f₂.comp b →
        ∀ (o'' : LowObj D' c (f₁.comp b)) (m₁ : ObjMap o'' o (spMap f₁)) (m₂ : ObjMap o'' o (spMap f₂))
          (z : X → (Sp A ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f₁ ≫ (x₀ y).left) →
          (∀ y, z y ≫ m₂.toSABMap.φ = spMap f₂ ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f₁ = f₂) ∧
        (∀ (k : Type) [Field k] (f : W →+* DualNumber k) (o'' : LowObj D' c (f.comp b)) (m₁ : ObjMap o'' o (spMap f))
          (m₂ : ObjMap o'' o (spMap (GlobalTheory.RigChart.constHom f))) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)),
          (∀ y, z y ≫ m₁.toSABMap.φ = spMap f ≫ (x₀ y).left) →
          (∀ y, z y ≫ m₂.toSABMap.φ = spMap (GlobalTheory.RigChart.constHom f) ≫ (x₀ y).left) →
          (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f = GlobalTheory.RigChart.constHom f)) ∧
      (letI := ((residue W).comp b).toAlgebra
        ∃ a t : ℕ, ringKrullDim W = a ∧ Algebra.trdeg c.F (ResidueField W) = t ∧ a + t = N) := by
  obtain ⟨v, m0, hvg, hvx⟩ := hex V bV o' x hx hxl
  obtain ⟨hreg, b, hqb, hft, hdim⟩ :=
    GlobalTheory.SmoothStalk.stalk_regular_essFiniteType_dim c.F Cs g N hsm (v (closedPoint V))
  haveI : IsDomain (Cs.presheaf.stalk (v (closedPoint V))) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  obtain ⟨q, hq⟩ : ∃ q, q = Cs.fromSpecStalk (v (closedPoint V)) := ⟨_, rfl⟩
  rw [← hq] at hqb
  have hs : lowMap c b = q ≫ g ≫ lowMap c (RingHom.id c.F) := by
    rw [lowMap_eq c b, ← hqb, Category.assoc]
  obtain ⟨o, ⟨mq⟩⟩ := (obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).1
    (g ≫ lowMap c (RingHom.id c.F)) oC q (lowMap c b) hs
  have hsec := fun y => exists_section_pull mq.toSABMap.cart (u y)
  choose x₀ hx₀ using hsec
  set θ₀ : Cs.presheaf.stalk (v (closedPoint V)) →+* V := (Scheme.stalkClosedPointTo v).hom with hθ₀
  have hθq : spMap θ₀ ≫ q = v := by
    rw [hq]
    simpa [hθ₀, spMap] using Scheme.Spec_stalkClosedPointTo_fromSpecStalk v
  have hθb : θ₀.comp b = bV := by
    apply spMap_injective
    rw [spMap_comp', ← hqb, ← Category.assoc, hθq, hvg]
  obtain ⟨m0', hm0'⟩ := objMap_congr hθq.symm m0
  obtain ⟨n, hn⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o' q (spMap θ₀) mq).2 m0'
  have hmono : ∀ {T : Scheme.{0}} (a₁ a₂ : T ⟶ Sp (Cs.presheaf.stalk (v (closedPoint V)))), a₁ ≫ q = a₂ ≫ q → a₁ = a₂ :=
    fun a₁ a₂ h => by rw [hq] at h; exact (cancel_mono _).1 h
  refine ⟨Cs.presheaf.stalk (v (closedPoint V)), inferInstance, inferInstance, hreg, b, o, x₀, θ₀, n, hft, ?_, ?_, ?_, hθb, ?_, ⟨?_, ?_⟩, hdim⟩
  · intro y z
    apply hom_ext_pull mq.toSABMap.cart
    rw [hx₀, hadd, pull_mul mq.toSABMap.cart _ _ _ _ (hx₀ y) (hx₀ z)]
  · intro a y
    apply hom_ext_pull mq.toSABMap.cart
    rw [hx₀, hlin, Over.comp_left, Over.comp_left, Category.assoc, mq.toSABMap.act a, reassoc_of% (hx₀ y)]
  · exact inferInstance
  · intro y
    refine mq.toSABMap.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, ← hn, hm0', hvx, Category.assoc, hx₀, ← Category.assoc, hθq]
    · exact sec_comp_eq _ _ n.toSABMap.cart.1.w (x y) (x₀ y)
  · intro A _ _ f₁ f₂ hf o'' m₁ m₂ z hz₁ hz₂ _
    obtain ⟨k₁, hk₁⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o'' q (spMap f₁) mq).1 m₁
    obtain ⟨k₂, hk₂⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o'' q (spMap f₂) mq).1 m₂
    have hg : ∀ f : Cs.presheaf.stalk (v (closedPoint V)) →+* A, (spMap f ≫ q) ≫ g = spMap (f.comp b) := fun f => by
      rw [Category.assoc, hqb, spMap_comp']
    have e := huniq A (spMap f₁ ≫ q) (spMap f₂ ≫ q) (by rw [hg, hg, hf]) _ o'' k₁ k₂ z
      (by rw [lowMap_eq c (f₁.comp b), ← hg, Category.assoc])
      (fun y => by rw [hk₁, ← Category.assoc, hz₁, Category.assoc, hx₀, Category.assoc])
      (fun y => by rw [hk₂, ← Category.assoc, hz₂, Category.assoc, hx₀, Category.assoc])
    exact spMap_injective (hmono _ _ e)
  · intro k _ f o'' m₁ m₂ z hz₁ hz₂ _
    obtain ⟨k₁, hk₁⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o'' q (spMap f) mq).1 m₁
    obtain ⟨k₂, hk₂⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o'' q
      (spMap (GlobalTheory.RigChart.constHom f)) mq).1 m₂
    have hc : spMap (GlobalTheory.RigChart.constHom f) ≫ q = constPt (spMap f ≫ q) := by
      simp only [constPt, GlobalTheory.RigChart.constHom, spMap_comp', Category.assoc]
    obtain ⟨k₂', hk₂'⟩ := objMap_congr hc k₂
    have e := heps k (spMap f ≫ q) _ o'' k₁ k₂' z
      (by rw [lowMap_eq c (f.comp b), spMap_comp', ← hqb]; simp only [Category.assoc])
      (fun y => by rw [hk₁, ← Category.assoc, hz₁, Category.assoc, hx₀, Category.assoc])
      (fun y => by rw [hk₂', hk₂, ← Category.assoc, hz₂, Category.assoc, hx₀, ← Category.assoc, hc])
    rw [← hc] at e
    exact spMap_injective (hmono _ _ e)

end GlobalTheory.UCanon.BaseSch

namespace GlobalTheory.UCanon.BaseSch

theorem exists_baseSch_of_homScheme (hcs : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X], ∃ (Cs : Scheme.{0}) (g : Cs ⟶ Sp c.F) (oC : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) (g ≫ lowMap c (RingHom.id c.F))) (u : X → (𝟙_ (Over Cs) ⟶ oC.t.G)), SmoothOfRelativeDimension (D'.dim + Module.finrank (𝓞 E) X * (Module.finrank ℚ E / 2 * (D'.p + D'.q))) g ∧ (∀ y z, u (y + z) = u y * u z) ∧ (∀ (a : 𝓞 E) y, u (a • y) = u y ≫ oC.t.act.act a) ∧ (∀ (V : Type) [CommRing V] [IsReduced V] (bV : c.F →+* V) (o' : LowObj D' c bV) (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (v : Sp V ⟶ Cs) (m : ObjMap o' oC v), v ≫ g = spMap bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ = v ≫ (u y).left) ∧ (∀ (A : Type) [CommRing A] [IsReduced A] (v₁ v₂ : Sp A ⟶ Cs), v₁ ≫ g = v₂ ≫ g → ∀ (s' : Sp A ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v₁) (m₂ : ObjMap o'' oC v₂) (z : X → (Sp A ⟶ o''.t.G.left)), s' = v₁ ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v₁ ≫ (u y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = v₂ ≫ (u y).left) → v₁ = v₂) ∧ (∀ (k : Type) [Field k] (v : Sp (DualNumber k) ⟶ Cs) (s' : Sp (DualNumber k) ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v) (m₂ : ObjMap o'' oC (constPt v)) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)), s' = v ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v ≫ (u y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = constPt v ≫ (u y).left) → v = constPt v)) : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (bV : c.F →+* V) (o' : LowObj D' c bV) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsRegularLocalRing W) (b : c.F →+* W) (o : LowObj D' c b) (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ o.t.G)) (θ₀ : W →+* V) (m : ObjMap o' o (spMap θ₀)), b.EssFiniteType ∧ (∀ y z, x₀ (y + z) = x₀ y * x₀ z) ∧ (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ o.t.act.act a) ∧ IsLocalHom θ₀ ∧ θ₀.comp b = bV ∧ (∀ y, (x y).left ≫ m.toSABMap.φ = spMap θ₀ ≫ (x₀ y).left) ∧ ((∀ (A : Type) [CommRing A] [IsReduced A] (f₁ f₂ : W →+* A), f₁.comp b = f₂.comp b → ∀ (o'' : LowObj D' c (f₁.comp b)) (m₁ : ObjMap o'' o (spMap f₁)) (m₂ : ObjMap o'' o (spMap f₂)) (z : X → (Sp A ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f₁ ≫ (x₀ y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = spMap f₂ ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f₁ = f₂) ∧ (∀ (k : Type) [Field k] (f : W →+* DualNumber k) (o'' : LowObj D' c (f.comp b)) (m₁ : ObjMap o'' o (spMap f)) (m₂ : ObjMap o'' o (spMap (GlobalTheory.RigChart.constHom f))) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f ≫ (x₀ y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = spMap (GlobalTheory.RigChart.constHom f) ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f = GlobalTheory.RigChart.constHom f)) ∧ (letI := ((residue W).comp b).toAlgebra; ∃ a t : ℕ, ringKrullDim W = a ∧ Algebra.trdeg c.F (ResidueField W) = t ∧ a + t = D'.dim + Module.finrank (𝓞 E) X * (Module.finrank ℚ E / 2 * (D'.p + D'.q))) := by
  intro E _ _ _ H D' l c V _ _ _ bV o' X _ _ _ _ x hx hxl
  obtain ⟨Cs, g, oC, u, hsm, hadd, hlin, hex, huniq, heps⟩ := hcs D' c X
  exact of_homScheme D' c X Cs g oC u _ hsm hex huniq heps hadd hlin V bV o' x hx hxl

end GlobalTheory.UCanon.BaseSch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisionPointPairOverAlgClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_divisionPoint_pair_over_algClosed : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ (y : D.X) (x : TF (R := V) F ⟶ D.P.A), x ^ k = DegPre.cF D F y → ∃ p : QkPt D F k, p.y = y ∧ p.g.b = x := by
  first | exact @GlobalTheory.UCanon.exists_qk_over_cF | exact GlobalTheory.UCanon.exists_qk_over_cF | (intros; apply GlobalTheory.UCanon.exists_qk_over_cF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeRepresentingPolarizedHomsLocNoetStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteType_representing_polarizedHoms_locNoeth : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  first | (exact @GlobalTheory.HomFixGlue.homFix_finiteType) | (exact GlobalTheory.HomFixGlue.homFix_finiteType) | (intros; apply GlobalTheory.HomFixGlue.homFix_finiteType  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreKernelKilledOfBaseFaithfullyFlatStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_kernelKilled_of_base_faithfullyFlat : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → IsUnit ((d : ℕ) : Γ(T, ⊤)) → (∀ (T' : Over T) (x : T' ⟶ A'), (∃ s : (P'.pull (lift (snd A' T' ≫ x) (fst A' T')).left).Gen, s.IsGen) → x ^ d = 1) → ∀ t : T, GlobalTheory.KerKilledNear.FibreKilled d G P (g.base t) := by
  first | (exact @GlobalTheory.KerKilledFibre.fibreKilled_of_base) | (exact GlobalTheory.KerKilledFibre.fibreKilled_of_base) | (intros; apply GlobalTheory.KerKilledFibre.fibreKilled_of_base <;> assumption)
end

