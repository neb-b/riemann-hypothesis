module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIsogeny

open CommutatorPairing

section Gen

variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε ε' : K → ℤ}

theorem wchart_le_pow (d : ℕ) (j : K → L.ι) : LB.wchart L φ j ≤ LB.wchart (lbPow L d) φ (fun k _ => j k) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy k

theorem exists_gen_of_lbPow (d : ℕ) (hε : ∀ k, ε' k = ε k * d) (a : LB.Gen (LB.LinComb (lbPow L d) φ ε))
    (ha : a.IsGen) : ∃ u : LB.Gen (LB.LinComb L φ ε'), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L φ j →
        gm r z (LB.wchart L φ j) (u.s j) = gm r z (LB.wchart (lbPow L d) φ (fun k _ => j k)) (a.s fun k _ => j k) := by
  refine ⟨⟨fun j => res (wchart_le_pow d j) (a.s fun k _ => j k)⟩, fun j j' => unit_ext fun y hy => ?_,
    fun Z r z j hj => gm_res r z _ hj _⟩
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L φ ε' (𝟙 Y) y j j' hy.1 hy.2)
      ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))).symm))
  refine (gen_trans ha (𝟙 Y) y (wchart_le_pow d j hy.1) (wchart_le_pow d j' hy.2)).trans (congrArg (· * _) ?_)
  refine Finset.prod_congr rfl fun k _ => ?_
  have e := gm_linComb L (fun _ : PUnit => 𝟙 X) (fun _ => (d : ℤ)) (𝟙 Y ≫ φ k) y (fun _ => j k) (fun _ => j' k)
    (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.1 k) (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.2 k)
  rw [Fintype.prod_unique, Category.comp_id] at e
  refine (congrArg (· ^ ε k) e).trans ?_
  rw [hε, mul_comm (ε k), zpow_mul]

theorem exists_gen_pow (d : ℕ) (hε : ∀ k, ε' k = ε k * d) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L φ ε'), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), val u r z J = val t r z J ^ d := by
  refine ⟨⟨fun j => t.s j ^ d⟩, fun i j => ?_, fun Z r z J => map_pow _ _ _⟩
  have h := congrArg (· ^ d) (ht i j)
  simp only [mul_pow, ← map_pow] at h
  refine h.trans (congrArg₂ (· * ·) ?_ rfl)
  refine (Finset.prod_pow _ _ _).symm.trans (Finset.prod_congr rfl fun a _ => ?_)
  exact ((zpow_natCast _ _).symm.trans (zpow_mul _ _ _).symm).trans (congrArg _ (hε a).symm)

theorem exists_gen_move_pow {X₀ Y₀ : Scheme.{0}} {M : LB X₀} {F : X ⟶ X₀} (hL : L.IsLB) (hM : M.IsLB) {d : ℕ}
    (w : LB.Iso (lbPow L d) (M.pull F)) (hw : w.IsGen) (hε : ∀ k, ε' k = ε k * d) {φ₀ : K → (Y₀ ⟶ X₀)} (h : Y ⟶ Y₀)
    (hc : ∀ k, φ k ≫ F = h ≫ φ₀ k) (t : LB.Gen (LB.LinComb M φ₀ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L φ ε'), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J₀),
      Good L z J → Good M z J₀ → val t (r ≫ h) z J₀ =
        (∏ k, (fun χ : Z ⟶ X => gw w χ z (J₀ (χ ≫ F)) (fun _ => J χ)) (r ≫ φ k) ^ ε k) * val u r z J := by
  obtain ⟨b, hb, hm⟩ := H1.exists_gen_move hM (DVR.linComb_isLB L hL _ _) w ((isGen_iff w).1 hw) φ₀ φ ε h hc t ht
  obtain ⟨u, hu, hv⟩ := exists_gen_of_lbPow d hε b hb
  refine ⟨u, hu, fun Z r z J J₀ hJ hJ₀ => ?_⟩
  have m := hm _ r z (fun i => J₀ ((r ≫ φ i) ≫ F)) (fun i _ => J (r ≫ φ i))
    (fun i => hJ₀ ((r ≫ φ i) ≫ F)) (fun i => Set.mem_iInter.2 fun _ => hJ (r ≫ φ i))
  exact (val_of t _ z J₀ _ (fun i => congrArg J₀ (by rw [Category.assoc, Category.assoc, hc]))).trans
    (m.trans (congrArg (_ * ·) (hv _ r z _ (hJ.mem φ r)).symm))

end Gen

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

theorem weilIs_of_local (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {k : ℤ} {T : Over S}
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ}
    (h : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θx θy : ThetaGrp A L k (overRes V),
      θx.pt = overResι V ≫ x ∧ θy.pt = overResι V ≫ y ∧ CommIsOf A L k θx θy (unitRes V c)) :
    WeilIs A L k x y c := by
  intro p
  obtain ⟨V, hV, θx, θy, ex, ey, H⟩ := h p
  refine ⟨V, hV, ⟨θx, θy, ex, ey⟩, fun θ θ' e e' => (commIsOf_iff hL _ _ _).2 fun Z t b z J hJ => ?_⟩
  exact (commVal_indep hG hA hL θ θ' θx θy t t (by rw [e, ex]) (by rw [e', ey]) b z J hJ).trans
    ((commIsOf_iff hL _ _ _).1 H _ t b z J hJ)

theorem exists_theta_pow (d : ℕ) {n : ℤ} {T : Over S} (θ : ThetaGrp A L n T) :
    ∃ θ' : ThetaGrp A L (n * d) T, θ'.pt = θ.pt ∧ ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left) (J),
      thetaVal θ' t a z J = thetaVal θ t a z J ^ d := by
  obtain ⟨u, hu, hv⟩ := exists_gen_pow (L := L) (K := Fin 2) (φ := ![(snd T A).left, (translPt A θ.pt).left])
    (ε := ![n, -n]) (ε' := ![n * d, -(n * d)]) d (fun k => by fin_cases k <;> simp) θ.φ θ.isGen
  exact ⟨⟨θ.pt, u, hu⟩, rfl, fun Z t a z J => hv _ _ z J⟩

theorem weilIs_pow (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (d : ℕ) {n : ℤ} {T : Over S}
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (h : WeilIs A L n x y c) : WeilIs A L (n * d) x y (c ^ d) := by
  refine weilIs_of_local hG hA hL fun p => ?_
  obtain ⟨V, hV, ⟨θx, θy, ex, ey⟩, H⟩ := h p
  obtain ⟨θx', fx, vx⟩ := exists_theta_pow d θx
  obtain ⟨θy', fy, vy⟩ := exists_theta_pow d θy
  refine ⟨V, hV, θx', θy', fx.trans ex, fy.trans ey, (commIsOf_iff hL _ _ _).2 fun Z t a z J hJ => ?_⟩
  have e := (commIsOf_iff hL _ _ _).1 (H θx θy ex ey) Z t a z J hJ
  have e' : unitRes V (c ^ d) = unitRes V c ^ d := map_pow _ _ _
  rw [e', map_pow, ← e, commVal, commVal, vx, vx, vy, vy, fx, fy]
  simp only [mul_pow, inv_pow]

theorem exists_theta_pull (hL : L.IsLB) (hM : M.IsLB) (ψ : A ⟶ B) [IsMonHom ψ] {d : ℕ}
    (w : LB.Iso (lbPow L d) (M.pull ψ.left)) (hw : w.IsGen) {n : ℤ} {T : Over S} (x : T ⟶ A)
    (θ₀ : ThetaGrp B M n T) (hx : θ₀.pt = x ≫ ψ) :
    ∃ θ : ThetaGrp A L (n * d) T, θ.pt = x ∧ ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left) (J J₀),
      Good L z J → Good M z J₀ → thetaVal θ₀ t (a ≫ ψ) z J₀ =
        gw w a.left z (J₀ (a ≫ ψ).left) (fun _ => J a.left) ^ n *
          gw w ((t ≫ x) * a).left z (J₀ (((t ≫ x) * a) ≫ ψ).left) (fun _ => J ((t ≫ x) * a).left) ^ (-n) *
          thetaVal θ t a z J := by
  have hl : ∀ {Z : Over S} (t : Z ⟶ T) (a : Z ⟶ A), lift t a ≫ (T ◁ ψ) = lift t (a ≫ ψ) := fun t a => by simp
  have h₀ : snd T A ≫ ψ = (T ◁ ψ) ≫ snd T B := by simp
  have h₁ : translPt A x ≫ ψ = (T ◁ ψ) ≫ translPt B θ₀.pt := by
    show ((fst T A ≫ x) * snd T A) ≫ ψ = (T ◁ ψ) ≫ ((fst T B ≫ θ₀.pt) * snd T B)
    rw [MonObj.comp_mul, MonObj.mul_comp, hx]
    simp
  have hc : ∀ i : Fin 2, ![(snd T A).left, (translPt A x).left] i ≫ ψ.left =
      (T ◁ ψ).left ≫ ![(snd T B).left, (translPt B θ₀.pt).left] i := fun i => by
    fin_cases i
    · exact congrArg CommaMorphism.left h₀
    · exact congrArg CommaMorphism.left h₁
  obtain ⟨u, hu, hv⟩ := exists_gen_move_pow (ε := ![n, -n]) (ε' := ![n * d, -(n * d)]) hL hM w hw
    (fun k => by fin_cases k <;> simp) (T ◁ ψ).left hc θ₀.φ θ₀.isGen
  refine ⟨⟨x, u, hu⟩, rfl, fun Z t a z J J₀ hJ hJ₀ => ?_⟩
  have m := hv _ (lift t a).left z J J₀ hJ hJ₀
  rw [← Over.comp_left, hl, prod_theta x t a
    (fun χ : Z.left ⟶ A.left => gw w χ z (J₀ (χ ≫ ψ.left)) (fun _ => J χ))] at m
  exact m

theorem weilIs_pull_hom (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (hM : M.IsLB) (ψ : A ⟶ B)
    [IsMonHom ψ] {d : ℕ} (hw : LBIso (lbPow L d) (M.pull ψ.left)) {n : ℤ} {T : Over S} {x y : T ⟶ A}
    {c : Γ(T.left, ⊤)ˣ} (h : WeilIs B M n (x ≫ ψ) (y ≫ ψ) c) : WeilIs A L (n * d) x y c := by
  obtain ⟨w, hw⟩ := hw
  have := hA.comm
  refine weilIs_of_local hG hA hL fun p => ?_
  obtain ⟨V, hV, ⟨θx₀, θy₀, ex, ey⟩, H⟩ := h p
  obtain ⟨θx, fx, vx⟩ := exists_theta_pull hL hM ψ w hw (overResι V ≫ x) θx₀ (by rw [ex, Category.assoc])
  obtain ⟨θy, fy, vy⟩ := exists_theta_pull hL hM ψ w hw (overResι V ≫ y) θy₀ (by rw [ey, Category.assoc])
  refine ⟨V, hV, θx, θy, fx, fy, (commIsOf_iff hL _ _ _).2 fun Z t a z J hJ => ?_⟩
  choose J₀ hJ₀ using fun χ : Z.left ⟶ B.left => exists_chart hM (χ z)
  have e := (commIsOf_iff hM _ _ _).1 (H θx₀ θy₀ ex ey) Z t (a ≫ ψ) z J₀ hJ₀
  have gx : (t ≫ θx₀.pt) * (a ≫ ψ) = ((t ≫ overResι V ≫ x) * a) ≫ ψ := by
    rw [MonObj.mul_comp, ex]; simp only [Category.assoc]
  have gy : (t ≫ θy₀.pt) * (a ≫ ψ) = ((t ≫ overResι V ≫ y) * a) ≫ ψ := by
    rw [MonObj.mul_comp, ey]; simp only [Category.assoc]
  rw [← e, commVal, commVal, gx, gy, vx _ _ _ _ _ _ hJ hJ₀, vx _ _ _ _ _ _ hJ hJ₀, vy _ _ _ _ _ _ hJ hJ₀,
    vy _ _ _ _ _ _ hJ hJ₀, fx, fy, mul_left_comm (t ≫ overResι V ≫ y) (t ≫ overResι V ≫ x) a]
  simp only [zpow_neg]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.WeilIsogeny

namespace GlobalTheory

theorem weilIs_along_hom : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B)
    (L : LB A.left) (M : LB B.left) (d : ℕ) (n : ℤ) (T : Over S) (x y : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ),
    IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → IsMonHom ψ → LBIso (lbPow L d) (M.pull ψ.left) →
    Out.WeilIs B M n (x ≫ ψ) (y ≫ ψ) c' →
      Out.WeilIs A L (n * d) x y c' ∧ (Out.WeilIs A L n x y c → c' = c ^ d) := by
  intro hG S A B _ _ ψ L M d n T x y c c' hA _ hL hM hψ hw h
  have h' := WeilIsogeny.weilIs_pull_hom hG hA hL hM ψ hw h
  exact ⟨h', fun hc => CommutatorPairing.weilIs_unique hG hA hL h' (WeilIsogeny.weilIs_pow hG hA hL d hc)⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsInducedLocus
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {S : Scheme.{0}}

theorem exists_pair {G : Over S} [GrpObj G] {n m : ℕ} {La : Type} [AddCommGroup La] {Z₁ Z₂ : Over S}
    {e₁ : La → (Z₁ ⟶ G)} {e₂ : La → (Z₂ ⟶ G)} (R₁ : RepTors G n La Z₁ e₁) (R₂ : RepTors G m La Z₂ e₂) :
    ∃ (Z : Over S) (χ θ : La → (Z ⟶ G)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ a c, χ (a + c) = χ a * χ c) ∧
      (∀ a, χ a ^ n = 1) ∧ (∀ a c, θ (a + c) = θ a * θ c) ∧ (∀ a, θ a ^ m = 1) ∧
      (∀ (T : Over S) (u u' : T ⟶ Z), (∀ a, u ≫ χ a = u' ≫ χ a) → (∀ a, u ≫ θ a = u' ≫ θ a) → u = u') ∧
      ∀ (T : Over S) (χ' θ' : La → (T ⟶ G)), (∀ a c, χ' (a + c) = χ' a * χ' c) → (∀ a, χ' a ^ n = 1) →
        (∀ a c, θ' (a + c) = θ' a * θ' c) → (∀ a, θ' a ^ m = 1) →
        ∃ h : T ⟶ Z, (∀ a, h ≫ χ a = χ' a) ∧ ∀ a, h ≫ θ a = θ' a := by
  have := R₁.1
  have := R₁.2.1
  have := R₂.1
  have := R₂.2.1
  obtain ⟨h1, h2⟩ := finiteEtale_tensor Z₁ Z₂
  refine ⟨Z₁ ⊗ Z₂, fun a => fst _ _ ≫ e₁ a, fun a => snd _ _ ≫ e₂ a, h1, h2, fun a c => ?_, fun a => ?_,
    fun a c => ?_, fun a => ?_, fun T u u' hu hu' => ?_, fun T χ' θ' a1 p1 a2 p2 => ?_⟩
  · simp only [R₁.2.2.1, MonObj.comp_mul]
  · beta_reduce; rw [← MonObj.comp_pow, R₁.2.2.2.1, MonObj.comp_one]
  · simp only [R₂.2.2.1, MonObj.comp_mul]
  · beta_reduce; rw [← MonObj.comp_pow, R₂.2.2.2.1, MonObj.comp_one]
  · exact CartesianMonoidalCategory.hom_ext _ _ (R₁.ext fun a => by simpa using hu a)
      (R₂.ext fun a => by simpa using hu' a)
  · obtain ⟨z₁, hz₁, -⟩ := R₁.2.2.2.2 T χ' a1 p1
    obtain ⟨z₂, hz₂, -⟩ := R₂.2.2.2.2 T θ' a2 p2
    exact ⟨lift z₁ z₂, fun a => by simpa using hz₁ a, fun a => by simpa using hz₂ a⟩

variable {l : Level H}

theorem exists_induced_locus {B : Type} [Field B] {b : Base l B} {s : S ⟶ Sp B} (o : Obj D l b s) (l₂ : Level H)
    (b₂ : Base l₂ B)
    (hν : ∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ))
    (hL : ∀ (N : ℕ) (f : D.La →ₗ[𝓞 E] D.La) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) →
      (∀ a b, (N : ℤ) ∣ D.EF (f a) (f b) - ν * D.EF a b) →
      ∃ g : Sim D, (∀ a, D.ModN N (g.f N a - f a)) ∧ (N : ℤ) ∣ g.ν N - ν)
    (hM : ∀ (l : Level H) (N : ℕ) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) → (l.A : ℤ) ∣ ν - 1 →
      ∃ g : Sim D, (N : ℤ) ∣ g.ν N - ν ∧
      (l.A : ℤ) ∣ g.ν l.A - 1 ∧ (∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) ∧
      ∀ a, D.ModN l.A (g.f l.A a - a))
    (hT : ∀ n : ℕ, 0 < n → ∃ (Z : Over S) (et : D.La → (Z ⟶ o.t.G)), RepTors o.t.G n D.La Z et)
    (hW : ∀ (N : ℕ), 0 < N → ∀ (T : Over S) (x y : T ⟶ o.t.G) (c : Γ(T.left, ⊤)ˣ), IsUnit (N : Γ(T.left, ⊤)) →
      x ^ N = 1 → y ^ N = 1 → c ^ N = 1 → ClopenCond T fun _ h =>
        Out.WeilIs o.t.G o.t.PP.L N (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c))
    {e : 𝓞 E} (he : e ∈ Mc l₂) {Z : Over S} [IsFinite Z.hom] [Etale Z.hom] (χ θ : D.La → (Z ⟶ o.t.G))
    (hext : ∀ (T : Over S) (u u' : T ⟶ Z), (∀ a, u ≫ χ a = u' ≫ χ a) → (∀ a, u ≫ θ a = u' ≫ θ a) → u = u')
    (hex : ∀ (T : Over S) (χ' θ' : D.La → (T ⟶ o.t.G)), (∀ a c, χ' (a + c) = χ' a * χ' c) →
      (∀ a, χ' a ^ l₂.M = 1) → (∀ a c, θ' (a + c) = θ' a * θ' c) → (∀ a, θ' a ^ l₂.A = 1) →
        ∃ h : T ⟶ Z, (∀ a, h ≫ χ a = χ' a) ∧ ∀ a, h ≫ θ a = θ' a) :
    ∃ U : Z.left.Opens, IsClosed (U : Set Z.left) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S)
      (β : B →+* k), x ≫ s = spMap β → ∀ z : Over.mk x ⟶ Z, Set.range z.left ⊆ U ↔
        ∃ I : TateAt D o.t x, (I.ζ l₂.A : k) = β b₂.ζ ∧ (∀ a, z ≫ θ a = I.ev l₂.A a) ∧
          ∀ a, z ≫ χ a = I.ev l₂.M (e • a) := by
  have : CharZero B := ⟨fun m n h => by
    by_contra hne
    wlog hlt : n < m generalizing m n
    · exact this n m h.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) hne)
    have := (b.unit (m - n) (by omega)).ne_zero
    rw [Nat.cast_sub hlt.le, h, sub_self] at this
    exact this rfl⟩
  have hN : 0 < l₂.M' := Nat.lcm_pos (M_pos l₂) l₂.A_pos
  have hAN : l₂.A ∣ l₂.M' := Nat.dvd_lcm_right _ _
  have hMN : l₂.M ∣ l₂.M' := Nat.dvd_lcm_left _ _
  generalize l₂.M' = N at hN hAN hMN
  obtain ⟨L, _, _, ξ, _, hξ, hξA⟩ := exists_root_ext B hN hAN b₂.ζ_prim
  obtain ⟨ZN, et, R⟩ := hT N hN
  obtain ⟨W, α, _, _, hadd, hpow, HW⟩ := exists_full o.t s hN hξ.pow_eq_one R (hW N hN)
  obtain ⟨p, hp1, hp2⟩ := hex W (fun a => α (e • a) ^ (N / l₂.M)) (fun a => α a ^ (N / l₂.A))
    (fun a c => by rw [smul_add, hadd, mul_pow]) (fun a => by rw [← pow_mul, Nat.div_mul_cancel hMN, hpow])
    (fun a c => by rw [hadd, mul_pow]) (fun a => by rw [← pow_mul, Nat.div_mul_cancel hAN, hpow])
  obtain ⟨U, hU, HU⟩ := exists_image p
  refine ⟨U, hU, fun k _ _ x β hx z => (HU k x z).trans ?_⟩
  have hprim : ∀ β' : L →+* k, IsPrimitiveRoot (Units.map β'.toMonoidHom ξ) N := fun β' =>
    hξ.map_of_injective (Units.map_injective β'.injective)
  have hval : ∀ β' : L →+* k, β'.comp (algebraMap B L) = β →
      ((Units.map β'.toMonoidHom ξ ^ (N / l₂.A) : kˣ) : k) = β b₂.ζ := fun β' h => by
    rw [← h, RingHom.comp_apply, ← hξA, map_pow]
    rfl
  constructor
  · rintro ⟨w, rfl⟩
    have a1 : ∀ a c, w ≫ α (a + c) = w ≫ α a * w ≫ α c := fun a c => by rw [hadd, MonObj.comp_mul]
    have p1 : ∀ a, (w ≫ α a) ^ N = 1 := fun a => by rw [← MonObj.comp_pow, hpow, MonObj.comp_one]
    obtain ⟨β', hβ', h1, h2⟩ := (HW k x β hx (fun a => w ≫ α a) a1 p1).1 ⟨w, fun _ => rfl⟩
    obtain ⟨-, I₀, -⟩ := o.geom k x β hx
    obtain ⟨I, hI, hI'⟩ := exists_of_level hν N (hL N)
      (fun y y' c c' => weilIs_unique_fieldPoint _ _ _ o.t.PP.isLB k x N y y' c c') I₀ hN (hprim β')
      (fun a => w ≫ α a) a1 p1 h1 h2
    refine ⟨I, ?_, fun a => ?_, fun a => ?_⟩
    · rw [← zeta_pow_div I hN hAN, hI, hval β' hβ']
    · rw [Category.assoc, hp2, MonObj.comp_pow, ← hI', ev_pow_div I hN hAN]
    · rw [Category.assoc, hp1, MonObj.comp_pow, ← hI', ev_pow_div I hN hMN]
  · rintro ⟨I, h1, h2, h3⟩
    obtain ⟨β', hβ'⟩ : ∃ β' : L →+* k, β'.comp (algebraMap B L) = β := by
      letI : Algebra B k := β.toAlgebra
      exact ⟨(IsAlgClosed.lift : L →ₐ[B] k).toRingHom, (IsAlgClosed.lift : L →ₐ[B] k).comp_algebraMap⟩
    obtain ⟨I', g1, g2, g3⟩ := exists_adjust hν l₂ N (hM l₂ N) I hN hAN (hprim β')
      (Units.ext ((hval β' hβ').trans h1.symm))
    obtain ⟨w, hw⟩ := (HW k x β hx (I'.ev N) (I'.add N) (tateIso_ev_pow I' hN)).2
      ⟨β', hβ', I'.lin N, fun a c => g1 ▸ I'.isom N hN a c⟩
    refine ⟨w, hext _ _ _ (fun a => ?_) fun a => ?_⟩
    · rw [Category.assoc, hp1, MonObj.comp_pow, hw, ev_pow_div I' hN hMN, h3,
        g3 _ (Submodule.smul_mem_smul he Submodule.mem_top)]
    · rw [Category.assoc, hp2, MonObj.comp_pow, hw, ev_pow_div I' hN hAN, h2, g2]

structure LevStr {B : Type} [CommRing B] {b : Base l B} {s : S ⟶ Sp B} (o : Obj D l b s) {l₂ : Level H}
    (b₂ : Base l₂ B) (T : Over S) (χ θ : D.La → (T ⟶ o.t.G)) : Prop where
  add : ∀ a c, χ (a + c) = χ a * χ c
  ker : ∀ a ∈ l₂.Mb • (⊤ : Submodule (𝓞 E) D.La), χ a = 1
  addA : ∀ a c, θ (a + c) = θ a * θ c
  kerA : ∀ a, θ (l₂.A • a) = 1
  low : ∀ a, χ a ^ (l₂.M / l.M) = toUnit T ≫ o.eta a
  lowA : ∀ a, θ a ^ (l₂.A / l.A) = toUnit T ≫ o.etaA a
  geom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k), x ≫ s = spMap β →
    ∀ y : Over.mk x ⟶ T, ∃ I : TateAt D o.t x, (I.ζ l₂.A : k) = β b₂.ζ ∧ (∀ a, y ≫ θ a = I.ev l₂.A a) ∧
      ∀ a ∈ Mc l₂ • (⊤ : Submodule (𝓞 E) D.La), y ≫ χ a = I.ev l₂.M a

theorem add_map_idem {Q : Type} [Group Q] {l₂ : Level H} {e : 𝓞 E} (he' : 1 - e ∈ l₂.Mb) {f : D.La → Q}
    (hf : ∀ a c, f (a + c) = f a * f c) (hk : ∀ a ∈ l₂.Mb • (⊤ : Submodule (𝓞 E) D.La), f a = 1) (a : D.La) :
    f (e • a) = f a := by
  have : a = e • a + (1 - e) • a := by rw [← add_smul, add_sub_cancel, one_smul]
  conv_rhs => rw [this, hf, hk _ (Submodule.smul_mem_smul he' Submodule.mem_top), _root_.mul_one]

theorem exists_levStr_rep {B : Type} [Field B] {b : Base l B} {s : S ⟶ Sp B} (o : Obj D l b s) (l₂ : Level H)
    (b₂ : Base l₂ B) (hl : l.Dvd l₂) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A))
    (hν : ∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ))
    (hL : ∀ (N : ℕ) (f : D.La →ₗ[𝓞 E] D.La) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) →
      (∀ a b, (N : ℤ) ∣ D.EF (f a) (f b) - ν * D.EF a b) →
      ∃ g : Sim D, (∀ a, D.ModN N (g.f N a - f a)) ∧ (N : ℤ) ∣ g.ν N - ν)
    (hM : ∀ (l : Level H) (N : ℕ) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) → (l.A : ℤ) ∣ ν - 1 →
      ∃ g : Sim D, (N : ℤ) ∣ g.ν N - ν ∧
      (l.A : ℤ) ∣ g.ν l.A - 1 ∧ (∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) ∧
      ∀ a, D.ModN l.A (g.f l.A a - a))
    (hT : ∀ n : ℕ, 0 < n → ∃ (Z : Over S) (et : D.La → (Z ⟶ o.t.G)), RepTors o.t.G n D.La Z et)
    (hW : ∀ (N : ℕ), 0 < N → ∀ (T : Over S) (x y : T ⟶ o.t.G) (c : Γ(T.left, ⊤)ˣ), IsUnit (N : Γ(T.left, ⊤)) →
      x ^ N = 1 → y ^ N = 1 → c ^ N = 1 → ClopenCond T fun _ h =>
        Out.WeilIs o.t.G o.t.PP.L N (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c)) :
    ∃ (V : Over S) (χ θ : D.La → (V ⟶ o.t.G)), IsFinite V.hom ∧ Etale V.hom ∧ Surjective V.hom ∧
      LevStr o b₂ V χ θ ∧
      (∀ (T : Over S) (u u' : T ⟶ V), (∀ a, u ≫ χ a = u' ≫ χ a) → (∀ a, u ≫ θ a = u' ≫ θ a) → u = u') ∧
      ∀ (T : Over S) (χ' θ' : D.La → (T ⟶ o.t.G)), LevStr o b₂ T χ' θ' →
        ∃ h : T ⟶ V, (∀ a, h ≫ χ a = χ' a) ∧ ∀ a, h ≫ θ a = θ' a := by
  obtain ⟨hMM, hb, hAA⟩ := hl
  obtain ⟨e, he, he'⟩ := exists_idem l₂
  obtain ⟨Z₁, e₁, R₁⟩ := hT _ (M_pos l₂)
  obtain ⟨Z₂, e₂, R₂⟩ := hT _ l₂.A_pos
  obtain ⟨Z, χ, θ, _, _, a1, p1, a2, p2, hext, hex⟩ := exists_pair R₁ R₂
  obtain ⟨U, hU, HU⟩ := exists_induced_locus o l₂ b₂ hν hL hM hT hW he χ θ hext hex
  have q1 : ∀ a, o.eta a ^ l₂.M = 1 := fun a => by
    rw [← Nat.mul_div_cancel' hMM, pow_mul, ← add_map_nsmul o.eta_add, o.eta_ker _ (nsmul_M_mem l a), one_pow]
  have q2 : ∀ a, o.etaA a ^ l₂.A = 1 := fun a => by
    rw [← Nat.mul_div_cancel' hAA, pow_mul, ← add_map_nsmul o.etaA_add, o.etaA_ker, one_pow]
  have c1 := R₁.clopenCond (fun a => χ (e • a)) χ (fun a c => by rw [smul_add, a1]) (fun a => p1 _) a1 p1
  have c2 := R₁.clopenCond (fun a => χ a ^ (l₂.M / l.M)) (fun a => toUnit Z ≫ o.eta a)
    (fun a c => by rw [a1, mul_pow]) (fun a => by rw [pow_right_comm, p1, one_pow])
    (fun a c => by rw [o.eta_add, MonObj.comp_mul]) (fun a => by rw [← MonObj.comp_pow, q1, MonObj.comp_one])
  have c3 := R₂.clopenCond (fun a => θ a ^ (l₂.A / l.A)) (fun a => toUnit Z ≫ o.etaA a)
    (fun a c => by rw [a2, mul_pow]) (fun a => by rw [pow_right_comm, p2, one_pow])
    (fun a c => by rw [o.etaA_add, MonObj.comp_mul]) (fun a => by rw [← MonObj.comp_pow, q2, MonObj.comp_one])
  obtain ⟨U', hU', HU'⟩ := c1.and (c2.and c3)
  obtain ⟨V, i, hV1, hV2, hi, Hi⟩ := exists_sub (U ⊓ U') (hU.inter hU')
  have hir : Set.range i.left ⊆ (U : Set Z.left) ∩ U' := (Hi V i).2 ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨i1, i2, i3⟩ := (HU' V i).2 (hir.trans Set.inter_subset_right)
  have ia : ∀ a c, i ≫ χ (a + c) = i ≫ χ a * i ≫ χ c := fun a c => by rw [a1, MonObj.comp_mul]
  have univ : ∀ (T : Over S) (χ' θ' : D.La → (T ⟶ o.t.G)), LevStr o b₂ T χ' θ' →
      ∃ h : T ⟶ V, (∀ a, h ≫ i ≫ χ a = χ' a) ∧ ∀ a, h ≫ i ≫ θ a = θ' a := by
    intro T χ' θ' h
    obtain ⟨z, z1, z2⟩ := hex T χ' θ' h.add
      (fun a => by rw [← add_map_nsmul h.add, h.ker _ (nsmul_M_mem l₂ a)]) h.addA
      (fun a => by rw [← add_map_nsmul h.addA, h.kerA])
    obtain ⟨w, rfl⟩ := (Hi T z).1 (Set.subset_inter
      (range_subset_of_geom z U fun k _ _ x y => by
        obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
        obtain ⟨I, h1, h2, h3⟩ := h.geom k x β hβ y
        refine (HU k x β hβ _).2 ⟨I, h1, fun a => by rw [Category.assoc, z2, h2], fun a => ?_⟩
        rw [Category.assoc, z1, ← h3 _ (Submodule.smul_mem_smul he Submodule.mem_top),
          add_map_idem he' h.add h.ker])
      ((HU' T z).1 ⟨fun a => by rw [z1, z1, add_map_idem he' h.add h.ker],
        fun a => by rw [MonObj.comp_pow, z1, h.low, comp_toUnit_assoc],
        fun a => by rw [MonObj.comp_pow, z2, h.lowA, comp_toUnit_assoc]⟩))
    exact ⟨w, fun a => by rw [← z1, Category.assoc], fun a => by rw [← z2, Category.assoc]⟩
  refine ⟨V, fun a => i ≫ χ a, fun a => i ≫ θ a, hV1, hV2, ⟨fun pt => ?_⟩, ⟨ia, fun a ha => ?_, fun a c => ?_,
    fun a => ?_, fun a => ?_, fun a => ?_, fun k _ _ x β hx y => ?_⟩, fun T u u' h h' => ?_, univ⟩
  · obtain ⟨k, _, _, x, hx⟩ := FinEt.exists_algClosed_point S pt
    obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
    obtain ⟨-, I, h1, h2, h3⟩ := o.geom k x β hβ
    have hprim : IsPrimitiveRoot (β b₂.ζ) l₂.A := b₂.ζ_prim.map_of_injective β.injective
    obtain ⟨I', g1, g2, g3⟩ := exists_adjust hν l l₂.A (hM l l₂.A) I l₂.A_pos hAA
      (ξ := (hprim.isUnit l₂.A_pos.ne').unit) (IsPrimitiveRoot.coe_units_iff.1 (by simpa using hprim))
      (Units.ext (by rw [h1, hζ, map_pow, Units.val_pow_eq_pow_val, IsUnit.unit_spec]))
    have hc : Mc l₂ ≤ Mc l := Ideal.map_mono hb
    obtain ⟨z, z1, z2⟩ := hex (Over.mk x) (fun a => I'.ev l₂.M (e • a)) (I'.ev l₂.A)
      (fun a c => by rw [smul_add, I'.add]) (fun a => tateIso_ev_pow I' (M_pos l₂) _) (I'.add _)
      (tateIso_ev_pow I' l₂.A_pos)
    obtain ⟨w, -⟩ := (Hi _ z).1 (Set.subset_inter
      ((HU k x β hβ z).2 ⟨I', by rw [g1, IsUnit.unit_spec], z2, z1⟩)
      ((HU' _ z).1 ⟨fun a => by
          rw [z1, z1]
          exact add_map_idem he' (f := fun a => I'.ev l₂.M (e • a)) (fun a c => by rw [smul_add, I'.add])
            (fun a ha => (I'.ker _ (M_pos l₂) _).2 (modN_smul_Mb l₂ he ha)) a,
        fun a => by
          have hm : e • a ∈ Mc l • (⊤ : Submodule (𝓞 E) D.La) := Submodule.smul_mem_smul (hc he) Submodule.mem_top
          rw [MonObj.comp_pow, z1, ev_pow_div I' (M_pos l₂) hMM, g3 _ hm, ← h3 _ hm,
            add_map_idem (hb he') o.eta_add o.eta_ker, comp_toUnit_assoc],
        fun a => by rw [MonObj.comp_pow, z2, ev_pow_div I' l₂.A_pos hAA, g2, ← h2, comp_toUnit_assoc]⟩))
    obtain ⟨p, hp⟩ : pt ∈ Set.range x := by rw [hx]; rfl
    exact ⟨w.left p, by rw [← Scheme.Hom.comp_apply, Over.w w]; exact hp⟩
  · obtain ⟨c, hc⟩ := modN_smul_Mb l₂ he ha
    beta_reduce
    rw [← i1, hc, add_map_nsmul a1, p1, MonObj.comp_one]
  · beta_reduce
    rw [a2, MonObj.comp_mul]
  · beta_reduce
    rw [add_map_nsmul a2, p2, MonObj.comp_one]
  · beta_reduce
    rw [← MonObj.comp_pow, i2, comp_toUnit_assoc]
  · beta_reduce
    rw [← MonObj.comp_pow, i3, comp_toUnit_assoc]
  · obtain ⟨I, h1, h2, h3⟩ := (HU k x β hx (y ≫ i)).1 (by
      rintro _ ⟨p, rfl⟩
      exact (hir ⟨y.left p, by simp⟩).1)
    refine ⟨I, h1, fun a => by rw [← h2, Category.assoc], fun a ha => ?_⟩
    rw [← Category.assoc, h3]
    refine LevelTwist.ev_congr I (M_pos l₂) ?_
    obtain ⟨c, hc⟩ := modN_smul_Mc l₂ he' ha
    exact ⟨-c, by rw [smul_neg, ← hc, sub_smul, one_smul, neg_sub]⟩
  · exact (cancel_mono i).1 (hext _ _ _ (fun a => by simpa using h a) fun a => by simpa using h' a)

end GlobalTheory.LevCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPrimitiveRootMapOfNatCastNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.IntegersAway

theorem isPrimitiveRoot_map_of_natCast_ne_zero {R K : Type} [CommRing R] [IsDomain R] [CharZero R] [Field K] {k : ℕ}
    (hk : 0 < k) {z : R} (hz : IsPrimitiveRoot z k) (β : R →+* K) (hβ : (k : K) ≠ 0) : IsPrimitiveRoot (β z) k := by
  have : NeZero (k : K) := ⟨hβ⟩
  have h : (Polynomial.cyclotomic k R).IsRoot z := hz.isRoot_cyclotomic hk
  apply (Polynomial.isRoot_cyclotomic_iff (n := k) (R := K)).mp
  rw [← Polynomial.map_cyclotomic k β]
  exact h.map β

theorem exists_tBase_of_numberField {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ) {k : ℕ} (hk : 0 < k)
    {z r : F} (hz : IsPrimitiveRoot z k) (hr : IsIntegral ℤ r) :
    ∃ (o : Type) (_ : CommRing o) (b : TBase o k) (em : o →+* ℂ) (ρ : o) (_ : Algebra o F), ArBase em ∧
      IsFractionRing o F ∧ (∀ x, φ (algebraMap o F x) = em x) ∧ algebraMap o F ρ = r ∧
      algebraMap o F (b.ζ : o) = z := by
  obtain ⟨em, hem, hcomp⟩ := exists_arBase_away φ hk.ne'
  have hn' : (k : 𝓞 F) ≠ 0 := by exact_mod_cast hk.ne'
  have hM : Submonoid.powers (k : 𝓞 F) ≤ nonZeroDivisors (𝓞 F) := powers_le_nonZeroDivisors_of_noZeroDivisors hn'
  let o := Localization.Away (k : 𝓞 F)
  have hu : IsUnit (algebraMap (𝓞 F) F (k : 𝓞 F)) := by simpa using hk.ne'
  let j : o →+* F := IsLocalization.Away.lift (k : 𝓞 F) hu
  have hj : ∀ x, j (algebraMap (𝓞 F) o x) = algebraMap (𝓞 F) F x := IsLocalization.Away.lift_eq _ hu
  let alg : Algebra o F := j.toAlgebra
  have : IsScalarTower (𝓞 F) o F := IsScalarTower.of_algebraMap_eq fun x => (hj x).symm
  let z₀ : 𝓞 F := ⟨z, hz.isIntegral hk⟩
  have hz₀ : IsPrimitiveRoot z₀ k :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 F) F) hz RingOfIntegers.coe_injective
  have hko : IsUnit (k : o) := by
    simpa using IsLocalization.Away.algebraMap_isUnit (S := o) (k : 𝓞 F)
  have hzu : IsUnit (algebraMap (𝓞 F) o z₀) := (hz₀.isUnit hk.ne').map _
  refine ⟨o, inferInstance, ⟨hzu.unit, hko, fun K _ β => ?_⟩, em, algebraMap (𝓞 F) o ⟨r, hr⟩, alg, hem,
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (k : 𝓞 F)) o F, ?_, hj _, hj _⟩
  · refine isPrimitiveRoot_map_of_natCast_ne_zero hk hz₀ (β.comp (algebraMap (𝓞 F) o)) ?_
    simpa using (hko.map β).ne_zero
  · have : φ.comp j = em := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (k : 𝓞 F)) ?_
      rw [hcomp]
      ext x
      simp [hj]
    exact fun x => DFunLike.congr_fun this x

theorem exists_tBase_fractionRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H), ∃ (o : Type) (_ : CommRing o) (b : TBase o l.A) (em : o →+* ℂ) (ρ : o) (_ : Algebra o (KA l)), ArBase em ∧ IsFractionRing o (KA l) ∧ (∀ x, ((algebraMap o (KA l) x : KA l) : ℂ) = em x) ∧ algebraMap o (KA l) ρ = (baseKA l).ρ ∧ algebraMap o (KA l) (b.ζ : o) = (baseKA l).ζ := by
  intro E _ _ _ H l
  have : FiniteDimensional ℚ (KA l) := by
    refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
    rcases hx with rfl | rfl
    · refine IsIntegral.of_pow two_pos ?_
      rw [H.sqrt_neg_disc_sq]
      exact (isIntegral_algebraMap (x := (H.d : ℚ))).neg
    · refine IsIntegral.of_pow l.A_pos ?_
      rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
      exact isIntegral_one
  have : NumberField (KA l) := {}
  have hr : IsIntegral ℤ (baseKA l).ρ := by
    refine IsIntegral.of_pow two_pos ?_
    rw [(baseKA l).ρ_sq]
    simpa using (isIntegral_algebraMap (R := ℤ) (A := KA l) (x := (H.d : ℤ))).neg
  exact exists_tBase_of_numberField (KA l).val.toRingHom l.A_pos (baseKA l).ζ_prim hr

end GlobalTheory.ZM.IntegersAway
end

