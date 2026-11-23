module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.SqrtNegDiscMemCoeffField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalPair
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0510
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0762
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2960
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2423
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSysUOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2966

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryGenericFibreBoundaryChart
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_tateIso_roots {Dw : Datum H} (l : Level H) {k : Type} [Field k] {Q : Type} [Group Q]
    {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso Dw k Q act e) (z : ℕ → kˣ)
    (hz : ∀ n, 0 < n → IsPrimitiveRoot (z n) n) (hzp : ∀ n m, 0 < n → 0 < m → z (n * m) ^ m = z n)
    (hA : z l.A = I.ζ l.A) :
    ∃ I' : TateIso Dw k Q act e, (∀ n, 0 < n → I'.ζ n = z n) ∧ (∀ a, I'.ev l.A a = I.ev l.A a) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), I'.ev l.M a = I.ev l.M a := by
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with h0 | hpq
  · have hs : Subsingleton Dw.La := AllClasses.subsingleton_of_rank_zero Dw h0
    have hEF : ∀ a b : Dw.La, Dw.EF a b = 0 := fun a b => by
      rw [Subsingleton.elim a 0, map_zero, LinearMap.zero_apply]
    refine ⟨{ I with ζ := z, ζ_prim := hz, ζ_pow := hzp, isom := fun n hn a b => ?_ }, fun _ _ => rfl,
      fun _ => rfl, fun _ _ => rfl⟩
    simpa [hEF] using I.isom n hn a b
  · exact GlobalTheory.LocM.RootsPrescribe.roots E H Dw l k Q act e I z hpq hz hzp hA

theorem exists_genFib {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t)
    (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK t (jK R)) {S : Scheme.{0}} (t₀ : SAB H S)
    (z : Sp (FractionRing R) ⟶ S) (m2 : SABMap tK t₀ z) : letI := H.starRing;
    ∃ ψ₁ : P.A.A.left ⟶ tK.G.left, ψ₁ ≫ m1.φ = P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ∧
      IsGrpPullback P.A.A t₀.G z (ψ₁ ≫ m2.φ) ∧ LBIso P.A.L (t₀.PP.L.pull (ψ₁ ≫ m2.φ)) ∧
      ∀ a : 𝓞 E, (P.oA.act a).left ≫ ψ₁ ≫ m2.φ = (ψ₁ ≫ m2.φ) ≫ (t₀.act.act a).left := by
  letI := H.starRing
  have := P.U.gen_hom
  have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
  set k : P.A.A.left ⟶ t.G.left := P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) with hk
  have gpG : IsGrpPullback P.A.A t.G (jK R) k :=
    ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr (Category.id_comp _) rfl
  let ψ₁ : P.A.A.left ⟶ tK.G.left := m1.cart.1.lift k P.A.A.hom gpG.1.w
  have hψ₁ : ψ₁ ≫ m1.φ = k := m1.cart.1.lift_fst _ _ _
  have hψ₂ : ψ₁ ≫ tK.G.hom = P.A.A.hom := m1.cart.1.lift_snd _ _ _
  have n : IsGrpPullback P.A.A t.G (𝟙 _ ≫ jK R) (ψ₁ ≫ m1.φ) :=
    gpG.congr (Category.id_comp _).symm hψ₁.symm
  have cart1 : IsGrpPullback P.A.A tK.G (𝟙 _) ψ₁ := m1.cart.cancel n (hψ₂.trans (Category.comp_id _).symm)
  have cart : IsGrpPullback P.A.A t₀.G z (ψ₁ ≫ m2.φ) := (cart1.comp m2.cart).congr (Category.id_comp _) rfl
  have actA : ∀ x, (P.oA.act x).left ≫ k = k ≫ (t.act.act x).left := by
    intro x
    have e : P.oA.act x ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK R)).map (t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext x)).symm
    rw [hk, ← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have actK : ∀ a : 𝓞 E, (P.oA.act a).left ≫ ψ₁ = ψ₁ ≫ (tK.act.act a).left := by
    intro a
    apply m1.cart.1.hom_ext
    · calc ((P.oA.act a).left ≫ ψ₁) ≫ m1.φ = (P.oA.act a).left ≫ k := by rw [Category.assoc, hψ₁]
        _ = k ≫ (t.act.act a).left := actA a
        _ = (ψ₁ ≫ (tK.act.act a).left) ≫ m1.φ := by rw [Category.assoc ψ₁, m1.act a, ← Category.assoc, hψ₁]
    · rw [Category.assoc, hψ₂, Over.w (P.oA.act a), Category.assoc, Over.w (tK.act.act a), hψ₂]

  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have B₁ : LBIso (P.A.L.pull (𝟙 _)) (P.U.LG.L.pull k) :=
    LBIso.chartPull (chartPullSame P.A.L (fun _ => 𝟙 _) (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left
        (fun _ => hgi.symm))
      (chartPullSame P.U.LG.L (fun _ => k) (fun _ => pullback.fst t.G.hom (jK R)) _ P.U.gen.inv.left
        (fun _ => rfl)) P.U.ext
  have B₁' : LBIso P.A.L (t.PP.L.pull k) := by
    rw [← P.bundle]
    exact LBIso.chartPull (chartPullUnpull P.A.L (𝟙 _) rfl) (chartPullId _) B₁
  obtain ⟨w₂, -, g₂, -⟩ := rigIso_congr rfl m1.cm m1.lin rfl rfl
  have B₂ : LBIso (tK.PP.L.pull ψ₁) (t.PP.L.pull k) :=
    LBIso.chartPull (chartPullPull tK.PP.L ψ₁)
      (chartPullSame t.PP.L (fun _ => k) (fun _ => m1.φ) _ ψ₁ (fun _ => hψ₁.symm)) ⟨w₂, g₂⟩
  obtain ⟨w₃, -, g₃, -⟩ := rigIso_congr rfl m2.cm m2.lin rfl rfl
  have B₃ : LBIso (tK.PP.L.pull ψ₁) (t₀.PP.L.pull (ψ₁ ≫ m2.φ)) :=
    LBIso.chartPull (chartPullPull tK.PP.L ψ₁)
      (chartPullSame t₀.PP.L (fun _ => ψ₁ ≫ m2.φ) (fun _ => m2.φ) _ ψ₁ (fun _ => rfl)) ⟨w₃, g₃⟩
  have BL : LBIso P.A.L (t₀.PP.L.pull (ψ₁ ≫ m2.φ)) :=
    LBIso.trans P.A.isLB (pull_isLB tK.PP.isLB _) (pull_isLB t₀.PP.isLB _)
      (LBIso.trans P.A.isLB (pull_isLB t.PP.isLB _) (pull_isLB tK.PP.isLB _) B₁' (LBIso.symm B₂)) B₃
  refine ⟨ψ₁, hψ₁, cart, BL, fun a => ?_⟩
  rw [← Category.assoc, actK, Category.assoc, m2.act a, Category.assoc]

end GlobalTheory.LowDat

namespace GlobalTheory.LowDat

theorem exists_xfLevel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R)))
    (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F), GlobalTheory.LowDat.XFLevel C tK m1 m2 F I := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hR C tK m1 m2 F _ _ _
  letI := H.starRing
  have := hR.2
  have hT := GlobalTheory.FlatTors.torsionIso_holds E H R _ hR.1 C.t C.P
  have hM' : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  let β : KA l →+* F := (toF C F).comp (IntermediateField.inclusion c.le).toRingHom
  have hx : (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _) ≫ Xo.s = spMap β := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc C.y, C.y_over]
    simp only [β, toF, spMap_comp, Category.assoc]
  obtain ⟨-, J0, hζ0, jA, jM⟩ := Xo.univ.geom F (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _) β hx
  haveI := c.fin
  obtain ⟨w, hw1, hw2, hw3⟩ := GlobalTheory.HostModel.exists_roots c.F F (toF C F)
  have hwA : w l.A = J0.ζ l.A := Units.ext (by
    rw [hw3 l.A l.A_pos ⟨zeta l.A, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩ rfl, hζ0]
    rfl)
  obtain ⟨J, hJζ, hJA, hJM⟩ := exists_tateIso_roots l J0 w hw1 hw2 hwA
  obtain ⟨ψ₁, h1, gψ, lψ, aψ⟩ := exists_genFib C.P tK m1 Xo.univ.t (C.y ≫ pullback.fst _ _) m2
  obtain ⟨I, hI, eI⟩ := GlobalTheory.ArcOfPoint.exists_tateIsoQ Dw hR.1 C.P hT Xo.univ.t _ _ gψ lψ aψ F J
  refine ⟨I, ?_, ?_⟩
  · rw [hI, hJζ _ hM', hw3 _ hM' ⟨zeta l.M', c.zeta_mem⟩ rfl]
  · intro k a σ hσ x hx
    have hk : 0 < k := by
      rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
      exacts [l.A_pos, by have := l.three_le; omega]
    have hJσ : toUnit _ ≫ σ = J.ev k a := by
      rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, ha, rfl⟩
      · rw [hJA]; exact jA a
      · rw [hJM a ha]; exact jM a ha
    obtain ⟨f, f₁, f₂, f₃, -⟩ := hT F k hk
    obtain ⟨e, he⟩ : ∃ e : (TFK (R := R) F ⟶ C.P.A.A) ≃*
        (Over.mk (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _) ⟶ Xo.univ.t.G),
        ∀ x, (e x).left = x.left ≫ ψ₁ ≫ m2.φ := GlobalTheory.LiePull.exists_pushEquiv gψ (TFK (R := R) F) _ rfl
    have hx' : (e.symm (J.ev k a)).left ≫ ψ₁ ≫ m2.φ = (J.ev k a).left := by
      rw [← he, MulEquiv.apply_symm_apply]
    have hxk : e.symm (J.ev k a) ^ k = 1 := by
      rw [← map_pow, (J.onto k hk _).2 ⟨a, rfl⟩, map_one]
    obtain ⟨p, hp⟩ := f₂ _ hxk
    have hpe := eI k hk a p _ hx' ((f₁ p _).2 hp.symm)
    have hxx : x = e.symm (J.ev k a) := by
      rw [(f₁ _ _).1 hx, ← hp]; exact ((f₃ _ _).2 hpe).symm
    refine ⟨x.left ≫ ψ₁, by rw [Category.assoc, h1], ?_⟩
    rw [Category.assoc, hxx, hx', ← hJσ, Over.comp_left]
    have ht : (toUnit (Over.mk (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _))).left =
        jFK (R := R) F ≫ C.y ≫ pullback.fst _ _ := by
      simpa using Over.w (toUnit (Over.mk (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _)))
    rw [ht]
    simp only [Category.assoc]

end GlobalTheory.LowDat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryOfPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelSpreadPt

theorem isOpen_compl_basicOpen_sub {X : Scheme.{0}} (a b : Γ(X, ⊤)) {k : ℕ} (hk0 : 0 < k) (ha : a ^ k = 1)
    (hb : b ^ k = 1) (hk : IsUnit (k : Γ(X, ⊤))) : IsOpen ((X.basicOpen (a - b) : Set X)ᶜ) := by
  let bu : Γ(X, ⊤)ˣ := Units.ofPowEqOne b k hb hk0.ne'
  have hbu : (bu : Γ(X, ⊤)) = b := rfl
  set u : Γ(X, ⊤) := a * ((bu⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) with hu_def
  have hab : a - b = b * (u - 1) := by
    have : b * ((bu⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) = 1 := by rw [← hbu]; exact bu.mul_inv
    rw [hu_def, mul_sub, _root_.mul_one, mul_left_comm, this, _root_.mul_one]
  have hu : u ^ k = 1 := by
    have : bu ^ k = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hbu, hb, Units.val_one])
    rw [hu_def, mul_pow, ha, _root_.one_mul, ← Units.val_pow_eq_pow_val, inv_pow, this, inv_one, Units.val_one]
  have hbo : X.basicOpen (a - b) = X.basicOpen (u - 1) := by
    rw [hab, Scheme.basicOpen_mul, ← hbu, Scheme.basicOpen_of_isUnit _ bu.isUnit, top_inf_eq]
  set g : Γ(X, ⊤) := ∑ i ∈ Finset.range k, u ^ i with hg
  have h1 : (u - 1) * g = 0 := by rw [hg, mul_comm, geom_sum_mul, hu, sub_self]
  obtain ⟨q, hq⟩ : (u - 1) ∣ g - k := by
    have : g - k = ∑ i ∈ Finset.range k, (u ^ i - 1) := by
      rw [hg, Finset.sum_sub_distrib]; simp
    rw [this]
    exact Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow u 1 i
  have hdis : X.basicOpen (u - 1) ⊓ X.basicOpen g = ⊥ := by
    rw [← Scheme.basicOpen_mul, h1, Scheme.basicOpen_zero]
  have e : (k : Γ(X, ⊤)) = g + (u - 1) * (-q) := by rw [mul_neg, ← hq]; ring
  have hcov : ⊤ ≤ X.basicOpen g ⊔ X.basicOpen (u - 1) := by
    calc (⊤ : X.Opens) = X.basicOpen (k : Γ(X, ⊤)) := (Scheme.basicOpen_of_isUnit _ hk).symm
      _ = X.basicOpen (g + (u - 1) * (-q)) := by rw [← e]
      _ ≤ X.basicOpen g ⊔ X.basicOpen ((u - 1) * (-q)) := Scheme.basicOpen_add_le _ _ _
      _ ≤ _ := sup_le_sup_left (by rw [Scheme.basicOpen_mul]; exact inf_le_left) _
  have hd : ∀ x, x ∈ X.basicOpen (u - 1) → x ∈ X.basicOpen g → False := fun x h h' => by
    have : x ∈ ((X.basicOpen (u - 1) ⊓ X.basicOpen g : X.Opens) : Set X) := by
      rw [TopologicalSpace.Opens.coe_inf]; exact ⟨h, h'⟩
    rw [hdis] at this; exact this
  have hc : ∀ x, x ∈ X.basicOpen g ∨ x ∈ X.basicOpen (u - 1) := fun x => by
    have : x ∈ ((X.basicOpen g ⊔ X.basicOpen (u - 1) : X.Opens) : Set X) := hcov trivial
    rwa [TopologicalSpace.Opens.coe_sup, Set.mem_union] at this
  have hs : ((X.basicOpen (u - 1) : Set X)ᶜ) = X.basicOpen g := by
    ext x
    simp only [Set.mem_compl_iff, SetLike.mem_coe]
    exact ⟨fun h => (hc x).resolve_right h, fun h h' => hd x h' h⟩
  rw [hbo, hs]
  exact (X.basicOpen g).isOpen

end GlobalTheory.LevelSpreadPt

namespace GlobalTheory

open LevelSpread LevelSpreadPt TorsRootParam

theorem exists_levelIsometry_of_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (A : Type) [CommRing A] [IsDomain A] (P : Out.PolAV (Sp A)) (act : 𝓞 E → (P.A ⟶ P.A)) (z : A) (κ : Type) (lam : κ → D.La) (pt : κ → (Out.baseOver (Sp A) ⟶ P.A)) (n m N : ℕ), 0 < n → 0 < N → Nonempty (ℚ →+* A) → z ^ N = 1 → (∀ i, pt i ^ N = 1) → (∀ a, IsMonHom (act a)) → (∃ (K : Type) (_ : Field K) (β : A →+* K) (ζ : Kˣ) (ev : D.La → (Over.mk (spMap β) ⟶ P.A)), IsPrimitiveRoot ζ n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a ^ n = 1) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act c) ∧ (∀ a c, Out.WeilIs P.A P.L n (ev a) (ev c) (unitOn (ζ ^ D.EF a c))) ∧ (ζ : K) ^ m = β z ∧ ∀ i, ev (lam i) ^ m = (Over.homMk (spMap β) (by simp) : Over.mk (spMap β) ⟶ Out.baseOver (Sp A)) ≫ pt i) → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : A →+* K), ∃ (ζ : Kˣ) (ev : D.La → (Over.mk (spMap β) ⟶ P.A)), IsPrimitiveRoot ζ n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a ^ n = 1) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act c) ∧ (∀ a c, Out.WeilIs P.A P.L n (ev a) (ev c) (unitOn (ζ ^ D.EF a c))) ∧ (ζ : K) ^ m = β z ∧ ∀ i, ev (lam i) ^ m = (Over.homMk (spMap β) (by simp) : Over.mk (spMap β) ⟶ Out.baseOver (Sp A)) ≫ pt i := by
  intro E _ _ _ H D A _ _ P act z κ lam pt n m N hn hN hQ hz hpt hact hex K _ _ β
  obtain ⟨K₀, _, β₀, ζ₀, ev₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hex
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  obtain ⟨hfree, hfin⟩ := LevCover.datum_free D
  have := P.isAb.comm
  obtain ⟨q₀⟩ := hQ
  have hnat : ∀ k : ℕ, 0 < k → IsUnit (k : Γ(Sp A, ⊤)) := fun k hk => by
    have h := (IsUnit.mk0 (k : ℚ) (Nat.cast_ne_zero.2 hk.ne')).map
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.comp q₀)
    rwa [map_natCast] at h
  have hK : ∀ {L : Type} [Field L] (ρ : A →+* L) (k : ℕ), 0 < k → (k : L) ≠ 0 := fun ρ k hk => by
    have h := (IsUnit.mk0 (k : ℚ) (Nat.cast_ne_zero.2 hk.ne')).map (ρ.comp q₀)
    rw [map_natCast] at h
    exact h.ne_zero
  have hn' := hnat n hn
  refine GlobalTheory.exists_levelIsometry_of_dense hL E H D (Sp A) P act A (𝟙 _) z κ lam pt n m hn ?_ K (spMap β) β
    (hK β n hn) (Category.comp_id _)
  let gp : Sp A := (⊥ : PrimeSpectrum A)
  refine Dense.mono ((Set.singleton_subset_iff (a := gp)).2 ?_) ?_
  rotate_left
  · refine dense_iff_closure_eq.2 (Set.eq_univ_of_forall fun p => ?_)
    exact specializes_iff_mem_closure.1 ((PrimeSpectrum.le_iff_specializes (⊥ : PrimeSpectrum A) p).1 bot_le)

  obtain ⟨Z₀, e₀, -, hZet, hadd, hpow, hrep⟩ := GlobalTheory.exists_finiteEtale_latticeTorsionHom (Sp A) P.A n D.La P.isAb hn'
  let s₀ : Z₀.left ⟶ Sp ℤ := specZIsTerminal.from _
  let p := pullback.fst s₀ (spMap (algebraMap ℤ (CycRing n)))
  let g := pullback.snd s₀ (spMap (algebraMap ℤ (CycRing n)))
  let Y : Over (Sp A) := Over.mk (p ≫ Z₀.hom)
  let π : Y ⟶ Z₀ := Over.homMk p rfl
  let et : D.La → (Y ⟶ P.A) := fun a => π ≫ e₀ a
  let c : Γ(Y.left, ⊤)ˣ := Units.map (LevCover.fnOn g).toMonoidHom (cycUnit hn)
  have hu : IsUnit (n : Γ(Y.left, ⊤)) := isUnit_natCast_of_hom Y.hom hn'
  have hadd' : ∀ a a', et (a + a') = et a * et a' := fun a a' => by
    simp only [et]; rw [hadd, MonObj.comp_mul]
  have hpow' : ∀ a, et a ^ n = 1 := fun a => by
    simp only [et]; rw [← MonObj.comp_pow, hpow, MonObj.comp_one]
  have hc : c ^ n = 1 := by rw [← map_pow, cycUnit_pow, map_one]
  have hflat : Flat Y.hom := by
    have : Module.Free ℤ (CycRing n) :=
      Module.Free.of_basis (AdjoinRoot.powerBasis' (Polynomial.cyclotomic.monic n ℤ)).basis
    have : Flat (spMap (algebraMap ℤ (CycRing n))) :=
      (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
    have : Flat Z₀.hom := inferInstance
    show Flat (p ≫ Z₀.hom)
    infer_instance

  have hq1 : ∀ {T : Over (Sp A)} (h : T ⟶ Y) (x y : Y ⟶ P.A), h ≫ (x * y⁻¹) = 1 ↔ h ≫ x = h ≫ y :=
    fun h x y => by rw [MonObj.comp_mul, GrpObj.comp_inv, mul_inv_eq_one]
  choose C1 hC1 HC1 using fun (b : 𝓞 E) (a : D.La) =>
    TorsionCover.exists_clopen_eq_one P.A P.isAb hn' (et (b • a) * (et a ≫ act b)⁻¹) (by
      haveI := hact b
      rw [mul_pow, inv_pow, hpow', ← MonObj.pow_comp, hpow', MonObj.one_comp, inv_one, _root_.mul_one])
  choose C2 hC2 HC2 using fun (a a' : D.La) => GlobalTheory.exists_clopen_weilIs_iff hL (Sp A) P n Y (et a) (et a')
    (c ^ D.EF a a') hn hu (hpow' _) (hpow' _)
    (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow])
  let qY : Y ⟶ Out.baseOver (Sp A) := Over.homMk Y.hom (by simp)
  have hnN : IsUnit ((n * N : ℕ) : Γ(Sp A, ⊤)) := hnat _ (Nat.mul_pos hn hN)
  choose C4 hC4 HC4 using fun i : κ =>
    TorsionCover.exists_clopen_eq_one P.A P.isAb hnN (et (lam i) ^ m * (qY ≫ pt i)⁻¹) (by
      have e1 : (et (lam i) ^ m) ^ (n * N) = 1 := by
        rw [← pow_mul, show m * (n * N) = n * (m * N) by ring, pow_mul, hpow', one_pow]
      have e2 : (qY ≫ pt i) ^ (n * N) = 1 := by
        rw [← MonObj.comp_pow, show n * N = N * n by ring, pow_mul, hpt, one_pow, MonObj.comp_one]
      rw [mul_pow, inv_pow, e1, e2, inv_one, _root_.mul_one])
  let w : Γ(Y.left, ⊤) := LevCover.fnOn Y.hom z
  let C3 : Set Y.left := (Y.left.basicOpen ((c : Γ(Y.left, ⊤)) ^ m - w) : Set Y.left)ᶜ
  have hC3 : IsOpen C3 := by
    refine isOpen_compl_basicOpen_sub _ _ (Nat.mul_pos hn hN) ?_ ?_ (isUnit_natCast_of_hom Y.hom hnN)
    · rw [← pow_mul, show m * (n * N) = n * (m * N) by ring, pow_mul, ← Units.val_pow_eq_pow_val, hc, Units.val_one,
        one_pow]
    · simp only [w]
      rw [← map_pow, show n * N = N * n by ring, pow_mul, hz, one_pow, map_one]
  let C : Set Y.left := (⋂ b, ⋂ a, C1 b a) ∩ (⋂ a, ⋂ a', (C2 a a' : Set Y.left)) ∩ C3 ∩ ⋂ i, C4 i
  have hgen : ∀ {y y' : Y.left}, y ⤳ y' → y' ∈ C → y ∈ C := by
    intro y y' hyy hy'
    simp only [C, Set.mem_inter_iff, Set.mem_iInter] at hy' ⊢
    obtain ⟨⟨⟨k1, k2⟩, k3⟩, k4⟩ := hy'
    exact ⟨⟨⟨fun b a => hyy.mem_open (hC1 b a).isOpen (k1 b a),
      fun a a' => hyy.mem_open (C2 a a').isOpen (k2 a a')⟩, hyy.mem_open hC3 k3⟩,
      fun i => hyy.mem_open (hC4 i).isOpen (k4 i)⟩
  have key : ∀ (F : Type) [Field F] (x : Sp F ⟶ Sp A) (ρ : A →+* F) (ζ : Fˣ) (h : Over.mk x ⟶ Y), x = spMap ρ →
      Units.map h.left.appTop.hom.toMonoidHom c = unitOn ζ →
      (((∀ (b : 𝓞 E) a, h ≫ et (b • a) = (h ≫ et a) ≫ act b) ∧
        (∀ a a', Out.WeilIs P.A P.L n (h ≫ et a) (h ≫ et a') (unitOn (ζ ^ D.EF a a'))) ∧ (ζ : F) ^ m = ρ z ∧
        ∀ i, (h ≫ et (lam i)) ^ m = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp A)) ≫ pt i) ↔
        Set.range h.left ⊆ C) := by
    intro F _ x ρ ζ h hx hζ
    have hw : h.left ≫ Y.hom = x := Over.w h
    have hq : h ≫ qY = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp A)) := Over.OverMorphism.ext hw
    have h3 := pow_eq_iff Y.hom h.left ρ (by rw [hw, hx]) z c ζ m hζ
    have hzk : ∀ k : ℤ, unitOn (ζ ^ k) = Units.map h.left.appTop.hom.toMonoidHom (c ^ k) := fun k => by
      rw [map_zpow, hζ, unitOn, unitOn, map_zpow]
    simp only [C, Set.subset_inter_iff, Set.subset_iInter_iff, and_assoc]
    refine and_congr (forall₂_congr fun b a => ?_) (and_congr (forall₂_congr fun a a' => ?_)
      (and_congr h3 (forall_congr' fun i => ?_)))
    · rw [← HC1 b a _ h, hq1, Category.assoc]
    · rw [← HC2 a a' _ h, hzk]
    · rw [← HC4 i _ h, hq1, ← hq, Category.assoc, MonObj.comp_pow]

  obtain ⟨ρ₀, hρ₀⟩ := exists_map_eq hn h₁
  obtain ⟨h₀, hh₀, -⟩ := hrep (Over.mk (spMap β₀)) ev₀ h₂ h₃
  let w₀ : Sp K₀ ⟶ Y.left := pullback.lift h₀.left (spMap ρ₀) (specZIsTerminal.hom_ext _ _)
  have hw₀ : w₀ ≫ p = h₀.left := pullback.lift_fst _ _ _
  have hw₀' : w₀ ≫ g = spMap ρ₀ := pullback.lift_snd _ _ _
  let y₀ : Over.mk (spMap β₀) ⟶ Y := Over.homMk w₀ (by
    show w₀ ≫ p ≫ Z₀.hom = spMap β₀
    rw [← Category.assoc, hw₀]
    exact Over.w h₀)
  have hy₀c : Units.map y₀.left.appTop.hom.toMonoidHom c = unitOn ζ₀ := by
    rw [← hρ₀]
    exact LevCover.map_fnOn g w₀ ρ₀ hw₀' (cycUnit hn)
  obtain rfl : (fun a => y₀ ≫ et a) = ev₀ := funext fun a => by
    apply Over.OverMorphism.ext
    show w₀ ≫ p ≫ (e₀ a).left = (ev₀ a).left
    rw [← Category.assoc, hw₀]
    exact congrArg (fun t => t.left) (hh₀ a)
  have hC₀ := (key K₀ (spMap β₀) β₀ ζ₀ y₀ rfl hy₀c).1 ⟨h₄, h₅, h₆, h₇⟩
  obtain ⟨v₀⟩ : Nonempty (Sp K₀) := inferInstance

  have hs : (⊥ : PrimeSpectrum A) ⤳ Y.hom (w₀ v₀) := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨y, hy, ey⟩ := Flat.generalizingMap Y.hom hs
  have hyC : y ∈ C := hgen hy (hC₀ ⟨v₀, rfl⟩)
  let k := AlgebraicClosure (Y.left.residueField y)
  let u : Sp k ⟶ Y.left := spMap (algebraMap (Y.left.residueField y) k) ≫ Y.left.fromSpecResidueField y
  obtain ⟨v⟩ : Nonempty (Sp k) := inferInstance
  have huy : ∀ v', u v' = y := fun v' => by
    have : u v' ∈ Set.range (Y.left.fromSpecResidueField y) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    rwa [Scheme.range_fromSpecResidueField] at this
  obtain ⟨ρ, hρ⟩ := LevCover.exists_spMap (A := k) (u ≫ Y.hom)
  let yk : Over.mk (u ≫ Y.hom) ⟶ Y := Over.homMk u rfl
  obtain ⟨ζ, hζ⟩ := exists_unitOn (K := k) (Units.map yk.left.appTop.hom.toMonoidHom c)
  have hprim : IsPrimitiveRoot ζ n := by
    obtain ⟨β', hβ'⟩ := LevCover.exists_spMap (A := k) (u ≫ g)
    have e1 := (LevCover.map_fnOn g u β' hβ' (cycUnit hn)).symm.trans hζ
    rw [← unitOn_inj e1]
    exact isPrimitiveRoot_map hn (hK ρ n hn) β'
  refine ⟨k, inferInstance, u ≫ Y.hom, ρ, ζ, fun a => yk ≫ et a, hK ρ n hn, ⟨v, ?_⟩, by rw [Category.comp_id, hρ],
    hprim, fun a a' => by beta_reduce; rw [hadd', MonObj.comp_mul],
    fun a => by beta_reduce; rw [← MonObj.comp_pow, hpow', MonObj.comp_one],
    (key k (u ≫ Y.hom) ρ ζ yk hρ hζ).2 ?_⟩
  · show Y.hom (u v) = _
    rw [huy v, ey]
  · rintro _ ⟨v', rfl⟩
    show u v' ∈ C
    rw [huy v']
    exact hyC

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionDescendedSemiAbelian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DescLBExt

theorem exists_lb_extension : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∃ M : LB G.left, M.IsLB ∧ LBIso (M.pull e) tF.PP.L := by
  intro E _ _ _ H Dw l Xo c φ h1 h2 h3 Z zs i OZ N d J S π j _ BD hU hpre tF hmap G _ _ e hsa he hch
  have hU' := hU
  obtain ⟨⟨-, -, -, -, -, -⟩, -, -, -, ⟨⟨hnorm, -⟩, hproj, -, hdense, -, -⟩, -⟩ := hU'
  have := hsa.smooth
  have := hsa.geomConnected
  have := hsa.quasiCompact
  have := hsa.separated
  haveI : LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    infer_instance
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  have hS : Geo.Tor.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff_pred S).mp hnorm
  haveI := GlobalTheory.IsNormalScheme.of_pred hS
  have hst := _root_.GlobalTheory.BdStalkExt.exists_extension_at_boundary Xo c φ h1 h2 h3 zs i OZ N d J π j BD hU hpre tF hmap G e hsa he hch
  exact _root_.GlobalTheory.RigLBDense.exists_extension_of_local_ext G.hom j hdense e tF.G.hom he.1 (eSec G) (eSec tF.G) (Over.w η[G]) (cubeMapOf he).e_comm
    tF.PP.L tF.PP.isLB tF.PP.rig tF.PP.rigGen fun x hx => by
      obtain ⟨Nx, hNx, hx'⟩ := hst x hx
      exact _root_.GlobalTheory.SpreadLB.exists_spread G.hom j e tF.G.hom he.1 tF.PP.L tF.PP.isLB x Nx hNx hx'

end GlobalTheory.DescLBExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemGenericPointsMemClosure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem exists_mem_genericPoints_mem_closure (X : Scheme.{0}) (x : X) : ∃ η ∈ genericPoints X, x ∈ closure {η} := by
  obtain ⟨u, hu, hxu⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x} isIrreducible_singleton
  have hc : IsClosed u := isClosed_of_mem_irreducibleComponents u hu
  have hi : IsIrreducible u := hu.prop
  have hg := hi.isGenericPoint_genericPoint_closure
  rw [hc.closure_eq] at hg
  refine ⟨hi.genericPoint, ?_, ?_⟩
  · show closure {hi.genericPoint} ∈ irreducibleComponents X
    rw [hg.def]; exact hu
  · rw [hg.def]; exact hxu rfl

theorem exists_uSetup_regular_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H),
    1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (x : Xo.XF c),
      ∃ (X' : USetup C) (w : X'.M.Z), X'.π w = C.i x ∧ X'.S.R ≤ X'.M.O w := by
  intro E _ _ _ H Dw hpq l Xo c C x
  obtain ⟨η, hη, hx⟩ := exists_mem_genericPoints_mem_closure (Xo.XF c) x
  obtain ⟨X, -, hX⟩ := GlobalTheory.UPoinc.GSetup.exists_uSetup E H Dw hpq l Xo c C η hη 0
  have hr : Set.range X.π = closure {C.i η} := GlobalTheory.UPoinc.USetup.range_π_eq E H Dw hpq l Xo c C X η _ hX rfl
  have hxr : C.i x ∈ Set.range X.π := by
    rw [hr, ← specializes_iff_mem_closure]
    exact (specializes_iff_mem_closure.2 hx).map C.i.continuous
  obtain ⟨w, hw⟩ := hxr
  obtain ⟨wi⟩ := nonempty_uWit X
  obtain ⟨U, c₀, hc, fg, frac, hth, hev, ρ', u', -, hwU, -, -, ⟨G, _, α, β, hα, hβ, hL, -⟩, hu'⟩ :=
    GlobalTheory.UPoinc.exists_urechart_affine E H Dw hpq l Xo c C X wi w ⟨x, hw.symm⟩
  let X' : USetup C :=
    { o₁ := X.o₁
      Ω₁ := X.Ω₁
      S := X.S.rechart c₀ hc (X.M.ringOn U) fg frac hth hev
      ρ := ρ'
      big := X.big
      u := u'
      pulled := ⟨G, _, α, β, hα, hβ, hL⟩
      gen := fun v => by rw [hu']; exact X.gen v
      M := X.M
      normal := X.normal
      π := X.π
      fin := X.fin
      comp := by
        rw [← Category.assoc, hu', X.comp]
        simp only [Category.assoc] }
  exact ⟨X', w, hw, RatModel.ringOn_le_O (M := X.M) hwU⟩

end GlobalTheory.UPoinc
end
end

