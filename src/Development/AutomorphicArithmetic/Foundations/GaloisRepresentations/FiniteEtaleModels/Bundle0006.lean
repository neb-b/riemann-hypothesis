module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0022
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0026
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BEtaPt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem ev_nsmul {G : GDatum} {k : Type} [Field k] {Q : Type} [Group Q] {act : G.O → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : GTateIso G k Q act e) (n c : ℕ) (x : G.La) :
    I.ev n (c • x) = I.ev n x ^ c := by
  induction c with
  | zero =>
    rw [zero_nsmul, pow_zero]
    have h := I.add n 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  | succ c ih =>
    rw [succ_nsmul, I.add, ih, pow_succ]

theorem UpperTheory.Gal.FiniteEtaleModels.etaPtB_holds :
    EtaPtB := by
  unfold UpperTheory.Gal.FiniteEtaleModels.EtaPtB
  intro p _ D G L R _ _ gb h X s N' N o' o ψ hT Ω _ _ z x y hv
  unfold UpperTheory.Gal.Int.Geo.IsTrans at hT
  obtain ⟨-, -, -, -, hgeo⟩ := hT
  obtain ⟨I', I'', h1, h2, hiff⟩ := hgeo Ω z (Spec.preimage (z ≫ s)).hom (by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage])
  have hN' : 0 < (N' : ℕ) := by
    have := N'.2.1
    omega
  have hN : 0 < (N : ℕ) := by
    have := N.2.1
    omega
  have key := (hiff _ (Nat.mul_pos hN' hN) (Nat.Coprime.mul_left N'.2.2 N.2.2)
    ((N : ℕ) • x) ((N' : ℕ) • y)).2 hv
  have ex : I'.ev ((N' : ℕ) * N) ((N : ℕ) • x) = I'.ev N' x := by
    have t1 := I'.tower (N' : ℕ) N hN' hN x
    have t2 := ev_nsmul I' ((N' : ℕ) * N) N x
    exact t2.trans t1
  have ey : I''.ev ((N' : ℕ) * N) ((N' : ℕ) • y) = I''.ev N y := by
    have t1 := I''.tower (N : ℕ) N' hN hN' y
    have t2 := ev_nsmul I'' ((N' : ℕ) * N) N' y
    rw [mul_comm] at t1
    exact t2.trans t1
  have key2 := (ex ▸ ey ▸ key : I'.ev N' x ≫ ψ = I''.ev N y)
  have e1 := h1 x
  have e2 := h2 y
  rw [← Category.assoc]
  exact (congrArg (fun f => f ≫ ψ) e1).trans (key2.trans e2.symm)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BLevOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.bLev_of :
    LatB → EtaPtB → UpperTheory.Gal.crystallineComparison.Mod.EtInj → BLev := by
  intro hLat hEta hInj p _ D G L _ E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hle hb _ h hint htj M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂
    C₁ C₂ W f mf _ e _ _ Tj P Ω _ _ x x' hj hy
  have atq' : AtPrime D q r 𝔴' := { S.atq with max := hmax, le := hle }
  refine hInj q (datAt S.atq S.sp) (Ow w) S.b N₀ X₂.lev.1 X₂.lev.2.1 X₂.M 𝔟₂ 1 X₂.Y X₂.π X₂.ov X₂.mπ _ _ _ ?_ ?_
  · have e₁ : ∀ z : Sp Ω ⟶ (T.M M₁).X, (z ≫ W.π ≫ C₂.j) ≫ X₂.π = z ≫ P.y ≫ Tj.t := fun z => by
      rw [P.yt]; simp only [Category.assoc]
    rw [e₁, e₁, reassoc_of% hy]
  · intro y₀
    obtain ⟨x₀, v, hv, e₀⟩ := hLat p D G L q r 𝔴' 𝔟₁ 𝔟₂ i h atq' htj hint hb X₁.lev.2.2.2.2 M₁ M₂ a₁ a₂ n₁.2 n₂.2 y₀
    have key : ∀ z : Sp Ω ⟶ (T.M M₁).X, (z ≫ W.π ≫ C₂.j) ≫ (X₂.Y.lv y₀).left ≫ X₂.mπ.φ =
        (z ≫ ((T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • x₀)).left ≫ P.fa) ≫ Tj.ψ.left ≫ Tj.mt.φ := fun z => by
      have h1 := congrArg (fun g => g.left) (hEta p D G L E gb h (T.M M₁).X (T.M M₁).s M₁ M₂ (T.M M₁).univ W.o W.ψ W.trans Ω z
        (algebraMap (𝓞 D.F) D.O a₁ • x₀) (algebraMap (𝓞 D.F) D.O a₂ • y₀) ⟨v, hv, e₀⟩)
      have ht : (toUnit (Over.mk z)).left = z := by simpa using Over.w (toUnit (Over.mk z))
      simp only [Over.comp_left, ht] at h1
      have h2 := W.φ.eta (algebraMap (𝓞 D.F) D.O a₂ • y₀)
      have h3 := C₂.lv y₀
      simp only [Category.assoc]
      rw [reassoc_of% P.sq, P.mt, reassoc_of% h1, reassoc_of% h2, reassoc_of% h3]
    have sec : ((T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • x₀)).left ≫ (T.M M₁).univ.A.hom = 𝟙 _ := by
      simpa using Over.w ((T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • x₀))
    have hA : x ≫ ((T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • x₀)).left ≫ P.fa =
        x' ≫ ((T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • x₀)).left ≫ P.fa := by
      refine Tj.ms.cart.1.hom_ext ?_ ?_
      · have h4 := C₁.lv x₀
        simp only [Category.assoc]
        rw [P.ms, reassoc_of% h4, reassoc_of% hj]
      · simp only [Category.assoc]
        rw [P.ca.1.w, reassoc_of% sec, hy]
    rw [key x, key x', hA]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BSecInj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt Pulled UKer)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.secInjG_of :
    UpperTheory.Gal.crystallineComparison.Mod.PulledEx → UpperTheory.Gal.crystallineComparison.Mod.PulledRead → UpperTheory.Gal.crystallineComparison.Mod.PullKer → UpperTheory.Gal.crystallineComparison.Mod.KerFromU → UpperTheory.Gal.crystallineComparison.Mod.IsoOfKer → SecInjG := by
  intro hPE hPR hPK hKU hIK p _ D R _ b N hN hNp hm r w j e hw hu hj he M T K _ _ _ x y y' hy hy' hK
  have hpK0 : IsUnit ((p : ℕ) : K) := by
    refine IsUnit.mk0 _ ?_
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpK : IsUnit ((p : ℕ) : Γ(Sp K, ⊤)) := by
    have := hpK0.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    simpa using this
  obtain ⟨o₁, ⟨m₁⟩⟩ := _root_.GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X (Sp K) M.s x M.univ
  obtain ⟨P⟩ := hPE p D R b N hN hNp M r w j (p ^ e) T (Sp K) x (x ≫ M.s) rfl o₁ m₁ y hy
  obtain ⟨P'⟩ := hPE p D R b N hN hNp M r w j (p ^ e) T (Sp K) x (x ≫ M.s) rfl o₁ m₁ y' hy'
  have hc : ∃ e', p ^ e = p ^ e' ∧ (0 < j → 0 < e') := ⟨e, rfl, he⟩
  have kernel_imp (z z' : Sp K ⟶ T.Y) (hz : z ≫ T.s = x) (hz' : z' ≫ T.s = x)
      (hpoint : ∀ a : Over.mk x ⟶ M.univ.A,
        ES.KilledBy M.univ w a → KerAt T z a.left → KerAt T z' a.left)
      (Q : Pulled T m₁ z) (Q' : Pulled T m₁ z') (U : Over (Sp K)) (g : U ⟶ o₁.A)
      (hg : UKer r o₁ Q.ψ U g) : UKer r o₁ Q'.ψ U g := by
    obtain ⟨S, -, i, -, -, hfin, het, -, -, hiff⟩ :=
      ES.KerUPart.exists_kerUPart p D R b N hN hNp hm r w j (p ^ e)
        hw hu hj hc (Sp K) (x ≫ M.s) hpK o₁ Q.o' Q.ψ Q.isog Q.tj
    refine ⟨?_, hg.2⟩
    obtain ⟨v, rfl⟩ := (hiff U g).1 hg
    suffices hi : i ≫ Q'.ψ = 1 by
      rw [Category.assoc, hi]
      simp
    have : IsReduced S.left := by
      have : IsAffine S.left := isAffine_of_isAffineHom S.hom
      have hE : (Scheme.Hom.appTop S.hom).hom.Etale :=
        HasRingHomProperty.appTop @Etale S.hom het
      have hF : IsField Γ(Sp K, ⊤) :=
        MulEquiv.isField (Field.toIsField K)
          (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv
      let : Field Γ(Sp K, ⊤) := hF.toField
      let := (Scheme.Hom.appTop S.hom).hom.toAlgebra
      have : Algebra.Etale Γ(Sp K, ⊤) Γ(S.left, ⊤) := hE.toAlgebra
      have : _root_.IsReduced Γ(S.left, ⊤) :=
        Algebra.FormallyUnramified.isReduced_of_field Γ(Sp K, ⊤) Γ(S.left, ⊤)
      exact isReduced_of_isAffine_isReduced S.left
    have : IsProper Q'.o'.A.hom := IsAbelianScheme.proper (self := Q'.o'.ab)
    have : Smooth Q'.o'.A.hom := IsAbelianScheme.smooth (self := Q'.o'.ab)
    have : LocallyOfFiniteType ((i ≫ Q'.ψ).left ≫ Q'.o'.A.hom) := by
      rw [Over.w]
      infer_instance
    apply Over.OverMorphism.ext
    refine ext_of_apply_eq Q'.o'.A.hom Set.univ isClosed_univ.isLocallyClosed dense_univ ?_ ?_
    · intro pt _ hpt
      let aK : 𝟙_ (Over (Sp K)) ⟶ S :=
        Over.homMk (pointOfClosedPoint S.hom pt hpt) (pointOfClosedPoint_comp S.hom pt hpt)
      let a := aK ≫ i
      have ha : UKer r o₁ Q.ψ _ a := (hiff _ _).2 ⟨aK, rfl⟩
      have hR := (hPR p D R b N M r w j (p ^ e) T (Sp K) x (x ≫ M.s) o₁ m₁ z hz Q a).1
      have hR' := (hPR p D R b N M r w j (p ^ e) T (Sp K) x (x ≫ M.s) o₁ m₁ z' hz' Q' a).1
      have hkw : ES.KilledBy o₁ w a := (Q.tj K (𝟙 _)).1 a ha.1 ha.2
      have hbase : (a.left ≫ m₁.φ) ≫ M.univ.A.hom = x := by
        rw [Category.assoc, m₁.cart.1.w, ← Category.assoc, Over.w a]
        exact Category.id_comp x
      let a₀ : Over.mk x ⟶ M.univ.A := Over.homMk (a.left ≫ m₁.φ) hbase
      have htransport := (hPK p D R b N M.X (Sp K) M.s (x ≫ M.s) x M.univ M.univ o₁ o₁ m₁ m₁
        (𝟙 _) (𝟙 _) (by simp)).1 (𝟙_ (Over (Sp K))) (Over.mk x) rfl a a₀ (by
          rw [eqToHom_refl, Category.id_comp]
          rfl)
      have hzero : a ≫ Q'.ψ = 1 := hR'.2 (hpoint a₀ ((htransport.2.2 w).1 hkw) (hR.1 ha.1))
      have hclosed : aK.left (IsLocalRing.closedPoint K) = pt := pointOfClosedPoint_apply S.hom pt hpt _
      have heq : aK ≫ (i ≫ Q'.ψ) = aK ≫ (1 : S ⟶ Q'.o'.A) := by
        rw [← Category.assoc, show aK ≫ i = a from rfl, hzero]
        simp
      rw [← hclosed]
      exact congrArg (fun f : 𝟙_ (Over (Sp K)) ⟶ Q'.o'.A => f.left (IsLocalRing.closedPoint K)) heq
    · rw [Over.w, Over.w]
  have k1 := kernel_imp y y' hy hy' (fun g hg => (hK g hg).1) P P'
  have k2 := kernel_imp y' y hy' hy (fun g hg => (hK g hg).2) P' P
  have hker : ∀ (U : Over (Sp K)) (g : U ⟶ o₁.A), g ≫ P.ψ = 1 ↔ g ≫ P'.ψ = 1 := by
    intro U g
    constructor
    · exact hKU p D R b N r w hw.ne_top hu K (x ≫ M.s) (p ^ e) o₁ P.o' P'.o' P.ψ P'.ψ P.isog P'.isog
        (fun U g => ⟨k1 U g, k2 U g⟩) U g
    · exact hKU p D R b N r w hw.ne_top hu K (x ≫ M.s) (p ^ e) o₁ P'.o' P.o' P'.ψ P.ψ P'.isog P.isog
        (fun U g => ⟨k2 U g, k1 U g⟩) U g
  obtain ⟨m, hm'⟩ := hIK p D R b N K (x ≫ M.s) (p ^ e) o₁ P.o' P'.o' P.ψ P'.ψ P.isog P'.isog hker
  obtain ⟨m'', hm''⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m P'.m'
  have hU := T.univ (Sp K) x o₁ P.o' m₁ P.ψ hpK P.isog P.tj
  have fix : ∀ (f : Sp K ⟶ T.Y) (_ : f = y') (n : GlobalTheory.UPel.HT.ObjMap P.o' T.o' f),
      ∃ n' : GlobalTheory.UPel.HT.ObjMap P.o' T.o' y', n'.φ = n.φ := by
    rintro f rfl n
    exact ⟨n, rfl⟩
  obtain ⟨n', hn'⟩ := fix _ (Category.id_comp y') m''
  refine hU.unique ⟨hy, P.m₀, P.m', P.sq⟩ ⟨hy', P'.m₀, n', ?_⟩
  rw [hn', hm'', ← Category.assoc, hm', P'.sq]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bezout
section
set_option autoImplicit false

namespace UpperTheory.Gal.FiniteEtaleModels.O

section Form

variable {M : Type} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M)

private lemma skew (alt : ∀ x, B x x = 0) (x y : M) : B x y = - B y x := by
  have h := alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, alt x, alt y, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

private lemma bezout {e n : ℕ} (hc : e.Coprime n) : ∃ a b : ℤ, a * e + b * n = 1 :=
  Nat.isCoprime_iff_coprime.2 hc

private lemma first {n e : ℕ} (hn : 0 < n) (hc : e.Coprime n) (nd : Function.Injective B)
    (perf : ∀ f : M →ₗ[ℤ] ℤ, ∃ x, B x = e • f) (x : M) (h : ∀ y, (n : ℤ) ∣ B x y) :
    ∃ z, x = n • z := by
  obtain ⟨a, b, hab⟩ := bezout hc
  let f : M →ₗ[ℤ] ℤ :=
    { toFun := fun y => B x y / n
      map_add' := fun y y' => by
        simp only [map_add (f := _)]
        exact Int.add_ediv_of_dvd_right (h y')
      map_smul' := fun c y => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc c (h y) }
  have hf : ∀ y, (n : ℤ) * f y = B x y := fun y => Int.mul_ediv_cancel' (h y)
  obtain ⟨w, hw⟩ := perf f
  have key : n • w = e • x := by
    apply nd
    ext y
    simp only [map_nsmul, LinearMap.smul_apply, hw, nsmul_eq_mul, ← hf]
    ring
  have key' : (e : ℤ) • x = (n : ℤ) • w := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, key]
  refine ⟨a • w + b • x, ?_⟩
  calc x = ((a * e + b * n : ℤ)) • x := by rw [hab, one_smul]
    _ = a • ((e : ℤ) • x) + b • ((n : ℤ) • x) := by rw [add_smul, mul_smul, mul_smul]
    _ = n • (a • w + b • x) := by
      rw [key', ← Nat.cast_smul_eq_nsmul ℤ n, smul_add, smul_comm a, smul_comm b]

private lemma second {n e : ℕ} (hc : e.Coprime n) (nd : Function.Injective B)
    (alt : ∀ x, B x x = 0) (perf : ∀ f : M →ₗ[ℤ] ℤ, ∃ x, B x = e • f) (h : M →+ M) :
    ∃ k : M →+ M, ∀ x y, (n : ℤ) ∣ B (h x) y - B x (k y) := by
  obtain ⟨a, b, hab⟩ := bezout hc
  let F : M → M →ₗ[ℤ] ℤ := fun y => (B.flip y) ∘ₗ h.toIntLinearMap
  have hF : ∀ y x, F y x = B (h x) y := fun y x => rfl
  choose w hw using fun y => perf (F y)
  have wadd : ∀ y y', w (y + y') = w y + w y' := by
    intro y y'
    apply nd
    ext x
    simp only [map_add (f := _), LinearMap.add_apply, hw, LinearMap.smul_apply, hF, smul_add]
  let k : M →+ M := AddMonoidHom.mk' (fun y => -(a • w y)) (by
    intro y y'
    simp only [wadd, smul_add, neg_add])
  refine ⟨k, fun x y => ?_⟩
  have h1 : B x (k y) = a * (e * B (h x) y) := by
    simp only [k, AddMonoidHom.mk'_apply, map_neg, map_zsmul, smul_eq_mul, skew B alt x (w y), hw,
      LinearMap.smul_apply, hF, nsmul_eq_mul]
    ring
  rw [h1]
  exact ⟨b * B (h x) y, by linear_combination (-(B (h x) y)) * hab⟩

private lemma third {n : ℕ} (hn : 0 < n) [Module.Finite ℤ M] (g : M →+ M)
    (inj : ∀ x z, g x = n • z → ∃ w, x = n • w) (x : M) : ∃ y z, g y = x + n • z := by
  classical
  let N : AddSubgroup M := (nsmulAddMonoidHom n).range
  have memN : ∀ y, y ∈ N ↔ ∃ z, n • z = y := fun y => by
    simp [N, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  have hle : N ≤ N.comap g := by
    intro y hy
    obtain ⟨z, rfl⟩ := (memN y).1 hy
    exact (memN _).2 ⟨g z, (map_nsmul g n z).symm⟩
  let G := QuotientAddGroup.map N N g hle
  haveI : AddGroup.FG M := Module.Finite.iff_addGroup_fg.1 inferInstance
  haveI : Finite (M ⧸ N) := by
    apply AddCommGroup.finite_of_fg_torsion
    intro u
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective u
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨n, hn, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact (memN _).2 ⟨y, rfl⟩
  have ginj : Function.Injective G := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro u hu
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective u
    rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff] at hu
    obtain ⟨z, hz⟩ := (memN _).1 hu
    obtain ⟨w, hw⟩ := inj y z hz.symm
    rw [QuotientAddGroup.eq_zero_iff]
    exact (memN _).2 ⟨w, hw.symm⟩
  obtain ⟨u, hu⟩ := Finite.injective_iff_surjective.1 ginj (QuotientAddGroup.mk x)
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective u
  rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq] at hu
  obtain ⟨z, hz⟩ := (memN _).1 hu
  exact ⟨y, -z, by rw [smul_neg, hz]; abel⟩

end Form

theorem adj : UpperTheory.Gal.FiniteEtaleModels.O.Adj := by
  intro q _ D e
  haveI := D.finLa
  obtain ⟨e', he', perf⟩ := D.perfP
  have hc : e'.Coprime (q ^ e) := Nat.Coprime.pow_right e he'
  have hn : 0 < q ^ e := pow_pos (Fact.out : Nat.Prime q).pos e
  have fst : ∀ x : D.La, (∀ y, ((q ^ e : ℕ) : ℤ) ∣ D.EF x y) → Cg (q ^ e) x 0 := by
    intro x hx
    obtain ⟨z, hz⟩ := first D.EF hn hc D.nondeg perf x hx
    exact ⟨z, by rw [zero_add]; exact hz⟩
  refine ⟨fst, ?_, ?_⟩
  · intro h
    obtain ⟨k, hk⟩ := second D.EF hc D.nondeg D.alt perf h.toAddMonoidHom
    refine ⟨k, hk, ?_⟩
    intro c y
    obtain ⟨z, hz⟩ := fst (k (c • y) - c • k y) (by
      intro x
      obtain ⟨b', hb'⟩ : ∃ b', MulOpposite.unop (D.star b') = c := ⟨_, D.star_star c⟩
      have e1 := hk x (c • y)
      have e2 := hk (b' • x) y
      have a1 : D.EF (h.toAddMonoidHom (b' • x)) y = D.EF (h.toAddMonoidHom x) (c • y) := by
        rw [LinearMap.toAddMonoidHom_coe, map_smul, D.adj, hb']
      have a2 : D.EF (b' • x) (k y) = D.EF x (c • k y) := by rw [D.adj, hb']
      rw [a1, a2] at e2
      rw [skew D.EF D.alt, map_sub, dvd_neg]
      have h5 := dvd_sub e2 e1
      rwa [sub_sub_sub_cancel_left] at h5)
    exact ⟨z, by rw [zero_add, sub_eq_iff_eq_add'] at hz; exact hz⟩
  · intro g hg
    have ginj : ∀ x z, g x = (q ^ e) • z → ∃ w, x = (q ^ e) • w := by
      intro x z hz
      apply first D.EF hn hc D.nondeg perf x
      intro y
      have h3 := hg x y
      rw [hz, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h3
      have h2 : ((q ^ e : ℕ) : ℤ) ∣ ((q ^ e : ℕ) : ℤ) * D.EF z (g y) := dvd_mul_right _ _
      have h4 := dvd_sub h2 h3
      rwa [sub_sub_cancel] at h4
    refine ⟨fun x ⟨z, hz⟩ => ?_, fun x => ?_⟩
    · obtain ⟨w, hw⟩ := ginj x z (by rw [hz, zero_add])
      exact ⟨w, by rw [zero_add]; exact hw⟩
    · obtain ⟨y, z, hyz⟩ := third hn g ginj x
      exact ⟨y, z, hyz⟩

end UpperTheory.Gal.FiniteEtaleModels.O
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IdemCore
section
open NumberField

namespace UpperTheory.Gal.FiniteEtaleModels.O

private theorem idem_core {A : Type} [CommRing A] (bar : A ≃+* A) (ω : A) (tr nm r : ℤ) (q : ℕ)
    (h1 : ω + bar ω = (tr : A)) (h2 : ω * bar ω = (nm : A))
    (hd : IsCoprime (q : ℤ) (tr ^ 2 - 4 * nm)) (hr : (q : ℤ) ∣ r ^ 2 - tr * r + nm)
    (u : Ideal A) (hu : u = Ideal.span {(q : A), ω - (r : A)}) :
    ∃ ε : ℕ → A, ∀ e : ℕ,
      1 - ε e ∈ u ^ e ∧ bar (ε e) ∈ u ^ e ∧ (∀ x ∈ u ^ e, (q : A) ^ e ∣ ε e * x) ∧
      (q : A) ^ e ∣ ε e + bar (ε e) - 1 ∧ (q : A) ^ e ∣ ε (e + 1) - ε e ∧
      ∀ (𝔞 : Ideal A), (∃ f : ℕ, u ^ f ≤ 𝔞) → (q : A) ^ e ∈ 𝔞 → u ^ e ≤ 𝔞 := by
  classical
  obtain ⟨m, hm⟩ := hr
  obtain ⟨s, t, hst⟩ := hd
  have hmA : (r : A) ^ 2 - (tr : A) * r + nm = (q : A) * m := by
    have := congrArg (fun z : ℤ => (z : A)) hm
    push_cast at this
    exact this
  have hstA : (s : A) * q + t * ((tr : A) ^ 2 - 4 * nm) = 1 := by
    have := congrArg (fun z : ℤ => (z : A)) hst
    push_cast at this
    exact this
  obtain ⟨v, hv⟩ : ∃ v : Ideal A, v = Ideal.span {(q : A), bar ω - (r : A)} := ⟨_, rfl⟩
  have hbb : bar (bar ω) = ω := by
    have := congrArg bar h1
    rw [map_add (f := _), map_intCast] at this
    linear_combination this - h1
  have Mu : Ideal.map bar u = v := by
    rw [hu, hv, Ideal.map_span, Set.image_pair, map_natCast, map_sub, map_intCast]
  have Mv : Ideal.map bar v = u := by
    rw [hu, hv, Ideal.map_span, Set.image_pair, map_natCast, map_sub, map_intCast, hbb]
  have pu : ∀ e, ∀ x ∈ u ^ e, bar x ∈ v ^ e := fun e x hx => by
    rw [← Mu, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem bar hx
  have pv : ∀ e, ∀ x ∈ v ^ e, bar x ∈ u ^ e := fun e x hx => by
    rw [← Mv, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem bar hx
  have hqu : (q : A) ∈ u := hu ▸ Ideal.subset_span (by simp)
  have hwu : ω - (r : A) ∈ u := hu ▸ Ideal.subset_span (by simp)
  have hwv : bar ω - (r : A) ∈ v := hv ▸ Ideal.subset_span (by simp)
  have hsup : u ⊔ v = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have hd' : (tr : A) - 2 * r ∈ u ⊔ v := by
      have := Ideal.add_mem _ (Ideal.mem_sup_left hwu) (Ideal.mem_sup_right hwv)
      convert this using 1
      linear_combination -h1
    have key : (1 : A) = (q : A) * ((s : A) - 4 * t * m) + (t : A) * ((tr : A) - 2 * r) * ((tr : A) - 2 * r) := by
      linear_combination -hstA - 4 * (t : A) * hmA
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_sup_left hqu)) (Ideal.mul_mem_left _ _ hd')
  have hmul : u * v ≤ Ideal.span {(q : A)} := by
    rw [hu, hv, Submodule.mul_le]
    intro x hx y hy
    rw [Ideal.mem_span_pair] at hx hy
    obtain ⟨c, d, rfl⟩ := hx
    obtain ⟨c', d', rfl⟩ := hy
    rw [Ideal.mem_span_singleton']
    refine ⟨c * c' * q + c * d' * (bar ω - r) + d * c' * (ω - r) + d * d' * m, ?_⟩
    linear_combination (-(d * d')) * (h2 - (r : A) * h1 + hmA)
  have hcop : ∀ f e, u ^ f ⊔ v ^ e = ⊤ := fun f e =>
    Ideal.isCoprime_iff_sup_eq.1 (IsCoprime.pow (Ideal.isCoprime_iff_sup_eq.2 hsup))
  have hinf : ∀ e, u ^ e ⊓ v ^ e ≤ Ideal.span {(q : A) ^ e} := fun e => by
    rw [← Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.2 (hcop e e)), ← mul_pow,
      ← Ideal.span_singleton_pow]
    exact Ideal.pow_right_mono hmul e
  have dv : ∀ e y, y ∈ u ^ e → y ∈ v ^ e → (q : A) ^ e ∣ y := fun e y hy1 hy2 =>
    Ideal.mem_span_singleton.1 (hinf e (Submodule.mem_inf.2 ⟨hy1, hy2⟩))
  have ex : ∀ e, ∃ b, b ∈ v ^ e ∧ 1 - b ∈ u ^ e := fun e => by
    have h1' : (1 : A) ∈ u ^ e ⊔ v ^ e := by rw [hcop e e]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1'
    exact ⟨b, hb, by rw [← hab, add_sub_cancel_right]; exact ha⟩
  choose ε hεv hεu using ex
  refine ⟨ε, fun e => ⟨hεu e, pv e _ (hεv e), ?_, ?_, ?_, ?_⟩⟩
  · intro x hx
    exact dv e _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ (hεv e))
  · apply dv e
    · have h3 := Ideal.sub_mem _ (pv e _ (hεv e)) (hεu e)
      convert h3 using 1
      ring
    · have h3 := Ideal.sub_mem _ (hεv e) (pu e _ (hεu e))
      convert h3 using 1
      rw [map_sub, map_one]
      ring
  · apply dv e
    · have h3 := Ideal.sub_mem _ (hεu e) (Ideal.pow_le_pow_right (Nat.le_succ e) (hεu (e + 1)))
      convert h3 using 1
      ring
    · exact Ideal.sub_mem _ (Ideal.pow_le_pow_right (Nat.le_succ e) (hεv (e + 1))) (hεv e)
  · rintro 𝔞 ⟨f, hf⟩ hq x hx
    have h1' : (1 : A) ∈ u ^ f ⊔ v ^ e := by rw [hcop f e]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1'
    have hx' : x = x * a + x * b := by rw [← mul_add, hab, mul_one]
    rw [hx']
    refine Ideal.add_mem _ (hf (Ideal.mul_mem_left _ _ ha)) ?_
    have h4 := dv e _ (Ideal.mul_mem_right _ _ hx) (Ideal.mul_mem_left _ _ hb)
    obtain ⟨c, hc⟩ := h4
    rw [hc]
    exact Ideal.mul_mem_right _ _ hq

end UpperTheory.Gal.FiniteEtaleModels.O

theorem UpperTheory.Gal.FiniteEtaleModels.O.idem :
    UpperTheory.Gal.FiniteEtaleModels.O.Idem := by
  intro q hq D r hr
  have hprime : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq.out
  exact UpperTheory.Gal.FiniteEtaleModels.O.idem_core D.bar D.ω D.tr D.nm r q D.tr_eq D.nm_eq
    (hprime.coprime_iff_not_dvd.2 D.disc_p) hr _ rfl
end

