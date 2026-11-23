module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2015
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransOfMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem tiso_congr {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase D.toG R}
    {S : Scheme.{0}} {s : S ⟶ Sp R} {N : ℕ} (o : GObj gb N s) {k : Type} [Field k] {t t' : Sp k ⟶ S} (e : t = t')
    (I : UpperTheory.Gal.Int.Geo.TIso o t) (hI : Ind o I) :
    ∃ J : UpperTheory.Gal.Int.Geo.TIso o t', Ind o J ∧ ∀ n x, (J.ev n x).left = (I.ev n x).left := by
  subst e
  exact ⟨I, hI, fun _ _ => rfl⟩

private theorem lbIso_hecke_lbPow_one {X : Scheme.{0}} {P : LB X} (hP : P.IsLB) : LBIso (Hecke.lbPow P 1) P := by
  have h1 : (Hecke.lbPow P 1).IsLB := LB.isLB_linComb hP _ _
  have h2 : (lbPow P 1).IsLB := GlobalTheory.isLB_lbPow hP 1
  have h3 : ((Hecke.lbPow P 1).pull (𝟙 X)).IsLB := pull_isLB h1 _
  exact LBIso.trans h1 h2 hP
    (LBIso.trans h1 h3 h2 (GlobalTheory.DescendedPrincipal.lbIso_pull_id h1).symm
      (GlobalTheory.BiextPairing.lbIso_lbPow_hecke hP 1).symm)
    (GlobalTheory.lbIso_lbPow_one hP)

theorem UpperTheory.Gal.G3.pTransOfMap :
    MultBasic → RelComp → TatePull → TransOfMap := by
  intro MB RC TP p _ D G L R _ _ gb S s N o o' m
  have hw : m.φ ≫ o'.A.hom = o.A.hom := by simpa using m.cart.1.w
  let θ : o.A ⟶ o'.A := Over.homMk m.φ hw
  have hθ : θ.left = m.φ := rfl
  refine ⟨θ, rfl, ?_⟩
  have hmon : IsMonHom θ :=
    GlobalTheory.AmpleRigid.isMonHom_of_mul_comp θ
      (fun T => GlobalTheory.AmpleRigid.mul_comp_of_grpPullback_id (T := T) θ m.cart)
  have hact : ∀ c, o.act.act c ≫ θ = θ ≫ o'.act.act c := by
    intro c
    ext
    simpa [θ] using m.act c
  haveI : IsIso m.φ := m.cart.1.isIso_fst_of_isIso
  haveI : IsIso θ := by
    have : IsIso ((Over.forget S).map θ) := by
      change IsIso m.φ
      infer_instance
    exact isIso_of_reflects_iso θ (Over.forget S)
  have hsq : Hecke.sq2 θ = m.φ₂ := by
    apply Hecke.ProdGalois.grpScheme_square_hom_ext_fst_snd
    · rw [Hecke.ProdGalois.grpSchemeSquareProductMap_comp_fst, m.sq.1, hθ]
    · rw [Hecke.ProdGalois.grpSchemeSquareProductMap_comp_snd, m.sq.2, hθ]
  have hmon' : IsMonHom (asIso θ).hom := hmon
  have hinvmon : IsMonHom (inv θ) := (inferInstance : IsMonHom (asIso θ).inv)
  refine ⟨hmon, hact, ⟨inv θ, 1, hinvmon, ?_, ?_, ?_, by simp⟩, ⟨1, by simp, ?_, ?_⟩, ?_⟩
  · intro c
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← hact c, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · rw [pow_one]
    exact IsIso.hom_inv_id θ
  · rw [pow_one]
    exact IsIso.inv_hom_id θ
  · refine ⟨?_⟩
    rw [hsq]
    exact LBIso.trans (LB.isLB_linComb o.isLB _ _) o.isLB (pull_isLB o'.isLB _)
      (lbIso_hecke_lbPow_one o.isLB) m.pol
  · exact (MB p).2.2 D G L 1 (Subgroup.one_mem _)
  · intro k _ _ t β ht
    obtain ⟨I₁, hI₁⟩ := o.geom k t β ht
    obtain ⟨I₂, hind, hev⟩ := (TP p D R gb S S s s (𝟙 S) (↑N) o' o m k t).2 I₁
    obtain ⟨J, hJ, hJe⟩ := tiso_congr o' (Category.comp_id t) I₂ (hind hI₁)
    refine ⟨I₁, J, hI₁, hJ, ?_⟩
    intro n hn hcop x y
    have key : I₁.ev n x ≫ θ = J.ev n x := by
      ext
      exact (hev n x).trans (hJe n x).symm
    rw [key]
    have hint : Integ L 1 := by
      intro v hv
      simpa using hv
    have hR := (RC p D G L R gb S s (↑N) (↑N) (↑N) o' o' o' k t J J J (𝟙 _) (𝟙 _) 1 1
      inferInstance inferInstance hint).1 n hn hcop x y
    simpa using hR
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem pow_push {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (d : ℕ) :
    ((𝟙 G') ^ d : G' ⟶ G').left ≫ φ = φ ≫ ((𝟙 G) ^ d : G ⟶ G).left := by
  obtain ⟨hpb, hm⟩ := h
  have hw : φ ≫ G.hom = G'.hom ≫ f := hpb.w
  let P : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ (by simpa using hw)
  have key : ∀ n : ℕ, ((𝟙 G') ^ n : G' ⟶ G').left ≫ φ = (P ^ n).left := by
    intro n
    induction n with
    | zero =>
      let x₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk ((1 : G' ⟶ G').left ≫ φ)
        (by rw [Category.assoc, hw, ← Category.assoc, Over.w]; rfl)
      have e : (x₀ * x₀).left = x₀.left := by
        rw [hm G' 1 1 x₀ x₀ rfl rfl, _root_.mul_one (1 : G' ⟶ G')]
        rfl
      have e2 : x₀ * x₀ = x₀ := Over.OverMorphism.ext e
      have e3 : x₀ = 1 := by simpa using e2
      rw [pow_zero, pow_zero]
      exact congrArg CommaMorphism.left e3
    | succ n ih =>
      rw [pow_succ, pow_succ, ← hm G' _ _ (P ^ n) P ih.symm (by simp [P])]
  rw [key d]
  have hP : P ≫ ((𝟙 G) ^ d) = P ^ d := by rw [MonObj.comp_pow, Category.comp_id]
  rw [← hP]
  rfl

private theorem qinv_pull {S S' : Scheme.{0}} {A₁' A₂' : Over S'} {A₁ A₂ : Over S} [GrpObj A₁'] [GrpObj A₁] {f : S' ⟶ S}
    {φ₁ : A₁'.left ⟶ A₁.left} {φ₂ : A₂'.left ⟶ A₂.left} (c₁ : IsGrpPullback A₁' A₁ f φ₁) {ψ : A₁ ⟶ A₂} {χ : A₂ ⟶ A₁}
    {ψ' : A₁' ⟶ A₂'} {χ' : A₂' ⟶ A₁'} (e : ψ'.left ≫ φ₂ = φ₁ ≫ ψ.left) (e' : χ'.left ≫ φ₁ = φ₂ ≫ χ.left) {d : ℕ}
    (h : ψ ≫ χ = (𝟙 A₁) ^ d) : ψ' ≫ χ' = (𝟙 A₁') ^ d := by
  apply Over.OverMorphism.ext
  apply c₁.1.hom_ext
  · rw [Over.comp_left, Category.assoc, e', ← Category.assoc, e, Category.assoc, ← Over.comp_left, h, pow_push c₁]
  · rw [Over.w, Over.w]

theorem UpperTheory.Gal.G3.pTransPull :
    HomPull → TatePull → TransPull := by
  intro hHom hTate p _ D G L R _ _ gb S S' s s' f hf N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ h hT
  obtain ⟨hmon, hact, ⟨χ, d, hχmon, hχact, e1, e2, hd⟩, ⟨c, hc, ⟨lb⟩, tt⟩, hgeo⟩ := hT
  obtain ⟨ψ', hψ, hmon', hact', hlb'⟩ := hHom D.toG R gb S S' s s' f N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ
  obtain ⟨χ', hχ, hχmon', hχact', -⟩ := hHom D.toG R gb S S' s s' f N₂ N₁ o₂ o₁ o₂' o₁' m₂ m₁ χ
  refine ⟨ψ', ⟨hmon' hmon, hact' hact, ⟨χ', d, hχmon' hχmon, hχact' hχact, qinv_pull m₁.cart hψ hχ e1,
    qinv_pull m₂.cart hχ hψ e2, hd⟩, ⟨c, hc, hlb' c ⟨lb⟩, tt⟩, ?_⟩, hψ⟩
  intro k _ _ t β ht
  obtain ⟨I₁, I₂, hI₁, hI₂, hev⟩ := hgeo k (t ≫ f) β (by rw [Category.assoc, hf, ht])
  obtain ⟨I₁', hI₁', hev₁⟩ := (hTate p D R gb S S' s s' f N₁ o₁ o₁' m₁ k t).1 I₁
  obtain ⟨I₂', hI₂', hev₂⟩ := (hTate p D R gb S S' s s' f N₂ o₂ o₂' m₂ k t).1 I₂
  refine ⟨I₁', I₂', hI₁' hI₁, hI₂' hI₂, fun n hn hnp x y => ?_⟩
  rw [← hev n hn hnp x y]
  constructor
  · intro e
    apply Over.OverMorphism.ext
    have key := congrArg (fun a => a.left ≫ m₂.φ) e
    simp only [Over.comp_left, Category.assoc, hψ] at key
    erw [← Category.assoc, hev₁ n x, hev₂ n y] at key
    rw [Over.comp_left]
    exact key
  · intro e
    apply Over.OverMorphism.ext
    apply m₂.cart.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hψ, ← Category.assoc]
      erw [hev₁ n x, hev₂ n y]
      rw [← Over.comp_left, e]
    · rw [Over.w, Over.w]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransSelf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem pol_one {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] [Algebra ℚ R]
    {gb : GBase D.toG R} {S : Scheme.{0}} {s : S ⟶ Sp R} {N : ℕ} (o : GObj gb N s) :
    Nonempty (LBIso (Hecke.lbPow o.P 1) (o.P.pull (Hecke.sq2 (𝟙 o.A)))) := by
  have h : Hecke.sq2 (𝟙 o.A) = 𝟙 _ := by simp [Hecke.sq2]
  refine ⟨?_⟩
  rw [h]
  unfold Hecke.lbPow LB.pull
  exact (GlobalTheory.PrimNorm.lbIso_iff o.isLB _ _ _ _).2 rfl

private theorem gTateIso_ev_nsmul' {G : GDatum} {k : Type} [Field k] {Q : Type} [Group Q]
    {act : G.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : GTateIso G k Q act e) (n c : ℕ)
    (y : G.La) : I.ev n (c • y) = I.ev n y ^ c := by
  induction c with
  | zero =>
    have h := I.add n 0 0
    rw [add_zero] at h
    have h1 : I.ev n 0 = 1 :=
      mul_left_cancel (a := I.ev n 0) (by rw [_root_.mul_one]; exact h.symm)
    rw [zero_smul, pow_zero, h1]
  | succ c ih => rw [succ_nsmul, I.add, ih, pow_succ]

theorem UpperTheory.Gal.G3.pTransSelf :
    MultBasic → RelComp → TateTwist → TransSelf := by
  intro hM hR hT p _ D G L R _ _ gb S s N
  refine ⟨fun o u hu => ?_, fun c hN hc o => ?_⟩
  · have hu1 : u ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu
    obtain ⟨a, a', ha, ha', haa, heq⟩ := (hM p).2.2 D G L u hu1
    refine ⟨⟨by simp, by simp⟩, fun _ => by simp, ⟨𝟙 _, 1, ⟨by simp, by simp⟩, fun _ => by simp,
      by simp, by simp, Nat.coprime_one_left _⟩, ⟨1, Nat.coprime_one_left _, pol_one o, a, a', ha,
      ha', haa, heq⟩, ?_⟩
    intro k _ _ x β hβ
    obtain ⟨I, hI⟩ := o.geom k x β hβ
    obtain ⟨J, hJ, hRel⟩ := hT p D G L R gb S s N o k x I hI u hu
    exact ⟨I, J, hI, hJ, hRel⟩
  · obtain ⟨a, a', ha, ha', haa, heq⟩ := (hM p).2.2 D G L 1 (one_mem _)
    have hmon : IsMonHom (𝟙 o.A) := ⟨by simp, by simp⟩
    refine ⟨show IsMonHom (𝟙 o.A) from hmon, fun _ => by simp [GObj.forgetMul],
      ⟨𝟙 _, 1, show IsMonHom (𝟙 o.A) from hmon,
      fun _ => by simp [GObj.forgetMul], by simp; exact Category.comp_id _,
      by simp; exact Category.comp_id _, Nat.coprime_one_left _⟩,
      ⟨1, Nat.coprime_one_left _, pol_one o, a, a', ha, ha', haa, heq⟩, ?_⟩
    intro k _ _ x β hβ
    obtain ⟨I, hI⟩ := o.geom k x β hβ
    have hInt : UpperTheory.Gal.Int.Geo.Integ L 1 := UpperTheory.Gal.Int.Geo.integ_of_mem (one_mem _)
    refine ⟨I, I, hI, fun y => ?_, ?_⟩
    · show toUnit _ ≫ o.eta (c • y) = _
      rw [hI, gTateIso_ev_nsmul', I.tower _ _ hN hc]
    · exact (hR p D G L R gb S s _ _ _ o o o k x I I I (𝟙 _) (𝟙 _) 1 1 hmon hmon hInt).1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwFEt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem card_eq_relIndex {G Γ : Type} [Group G] (H L : Subgroup G) (r : Γ → G) (hr : ∀ x, r x ∈ L)
    (hu : ∀ k ∈ L, ∃! x, k * (r x)⁻¹ ∈ H) : Nat.card Γ = H.relIndex L := by
  unfold Subgroup.relIndex Subgroup.index
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => (QuotientGroup.mk ⟨(r x)⁻¹, L.inv_mem (hr x)⟩ : L ⧸ H.subgroupOf L)) ⟨?_, ?_⟩)
  · intro x y e
    have e' := QuotientGroup.eq.mp e
    have h2 : r x * (r y)⁻¹ ∈ H := by simpa [Subgroup.mem_subgroupOf] using e'
    have h1 : r x * (r x)⁻¹ ∈ H := by simp [H.one_mem]
    exact (hu (r x) (hr x)).unique h1 h2
  · intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨x, hx, -⟩ := hu (g : G)⁻¹ (L.inv_mem g.2)
      refine ⟨x, QuotientGroup.eq.mpr ?_⟩
      rw [Subgroup.mem_subgroupOf]
      have h3 := H.inv_mem hx
      simpa using h3

private theorem fEt_normal (hb : FEtBasic) (hg : TwGal) {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G)
    (m j : X.ι) (b : X.admitted m j 1) (hn : ∀ k ∈ X.K j, ∀ u ∈ X.K m, k * u * k⁻¹ ∈ X.K m) :
    FEt (X.tr m j 1 b.1 b.2) ((X.K m).relIndex (X.K j)) := by
  obtain ⟨Γ, _, _, r, c, hr, hu, hG⟩ := hg X m j b hn
  rw [← card_eq_relIndex _ _ r hr hu]
  exact hb.2.2 _ Γ _ hG

theorem UpperTheory.Gal.G3.pTwFEt :
    FEtBasic → TwGal → TwFEt := by
  intro hb hg
  unfold TwFEt
  intro B G _ X i j a
  obtain ⟨m, hmj, hn, hS⟩ := X.deep j {(i, 1)}
  have hmi : X.K m ≤ X.K i := fun u hu => by simpa using hS (i, 1) (by simp) u hu
  have hij : X.K i ≤ X.K j := fun u hu => by simpa using a.2 u hu
  have b : X.admitted m j 1 := X.isAdmissibleIntegralBasisChange_one hmj
  have b' : X.admitted m i 1 := X.isAdmissibleIntegralBasisChange_one hmi
  have h1 := fEt_normal hb hg X m j b hn
  have h2 := fEt_normal hb hg X m i b' (fun k hk u hu => hn k (hij hk) u hu)
  have hc : X.tr m i 1 b'.1 b'.2 ≫ X.tr i j 1 a.1 a.2 = X.tr m j 1 b.1 b.2 := by
    have e : ∀ (h : G) (_ : h = 1) p q, X.tr m j h p q = X.tr m j 1 b.1 b.2 := by
      rintro _ rfl _ _; rfl
    rw [X.tr_mul m i j 1 1 b'.1 b'.2 a.1 a.2 (by simpa using a.1) (by simpa using b.2)]
    exact e _ (mul_one 1) _ _
  refine ⟨X.fin i j a.1 a.2, X.etale i j a.1 a.2, fun K _ _ x => ?_⟩
  set s := X.tr i j 1 a.1 a.2 with hs
  set r := X.tr m i 1 b'.1 b'.2 with hr
  have fs : Finite {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x} :=
    have := X.fin i j a.1 a.2
    (UpperTheory.Gal.TranscendenceTraces.fibFin_holds s K x).to_subtype
  have fr : ∀ y : {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x},
      Finite {w : Spec (CommRingCat.of K) ⟶ X.Z m // w ≫ r = y.1} := fun y =>
    have := X.fin m i b'.1 b'.2
    (UpperTheory.Gal.TranscendenceTraces.fibFin_holds r K y.1).to_subtype
  have := Fintype.ofFinite {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x}
  have e1 : {w : Spec (CommRingCat.of K) ⟶ X.Z m // w ≫ X.tr m j 1 b.1 b.2 = x} ≃
      Σ y : {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x},
        {w : Spec (CommRingCat.of K) ⟶ X.Z m // w ≫ r = y.1} :=
    { toFun := fun w => ⟨⟨w.1 ≫ r, by rw [Category.assoc, hc, w.2]⟩, ⟨w.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, by rw [← hc, ← Category.assoc, p.2.2, p.1.2]⟩
      left_inv := fun w => rfl
      right_inv := by
        rintro ⟨⟨y, hy⟩, ⟨w, hw⟩⟩
        change w ≫ r = y at hw
        subst hw
        rfl }
  have hcount : Nat.card {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x} * (X.K m).relIndex (X.K i) =
      (X.K m).relIndex (X.K j) := by
    rw [← h1.2.2 K x, Nat.card_congr e1, Nat.card_sigma]
    simp only [h2.2.2 K, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [Nat.card_eq_fintype_card]
  have hmul := Subgroup.relIndex_mul_relIndex (X.K m) (X.K i) (X.K j) hmi hij
  have hpos : 0 < (X.K m).relIndex (X.K i) := Nat.pos_of_ne_zero (X.idx m i)
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [hmul, ← hcount, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

namespace UpperTheory.Gal.G3

section Maps

open GlobalTheory.UPel.HT.Hecke

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

private theorem exists_map_id {b : GBase G R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : GObj b N s) :
    ∃ m : GObjMap o o (𝟙 S), m.φ = 𝟙 _ :=
  ⟨{ φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id o.A, sq := ⟨by simp, by simp⟩,
     act := fun c => by simp, pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB, eta := fun y => by simp }, rfl⟩

private theorem exists_map_comp {b : GBase G R} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R}
    {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂} {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (h₁ : GObjMap o₁ o₂ f) (h₂ : GObjMap o₂ o₃ g) : ∃ m : GObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

end Maps

end UpperTheory.Gal.G3

theorem UpperTheory.Gal.G3.pWitComp :
    TransSelf → TransComp → TransPull → WitComp := by
  intro hS hC hP
  intro p _ D G L R _ _ gb N₁ N₂ N₃ X₁ X₂ X₃ h h'
  refine ⟨fun u hu => ?_, fun hI hA π Φ π' Φ' hW hW' => ?_⟩
  · obtain ⟨m, hm⟩ := exists_map_id X₁.univ
    refine ⟨by simp, X₁.univ, 𝟙 _, m, (hS p D G L R gb X₁.X X₁.s N₁).1 X₁.univ u hu, ?_⟩
    rw [hm]
    simp
  · obtain ⟨hπ, o, ψ, φ, hT, hΦ⟩ := hW
    obtain ⟨hπ', o', ψ', φ', hT', hΦ'⟩ := hW'
    obtain ⟨o'', ⟨m''⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero X₁.s π hπ o'
    obtain ⟨ψ'', hT'', hsq⟩ := hP p D G L R gb X₂.X X₁.X X₂.s X₁.s π hπ _ _ X₂.univ o' o o'' φ m'' ψ' h' hT'
    have hTT := hC p D G L R gb X₁.X X₁.s N₁ N₂ N₃ X₁.univ o o'' ψ ψ'' h h' hI hA hT hT''
    obtain ⟨mm, hmm⟩ := exists_map_comp m'' φ'
    refine ⟨by rw [Category.assoc, hπ', hπ], o'', ψ ≫ ψ'', mm, hTT, ?_⟩
    rw [hmm, hΦ, hΦ', Over.comp_left, Category.assoc, Category.assoc, ← Category.assoc φ.φ, ← hsq,
      Category.assoc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitDeep
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitDeep :
    KNBasic → GenSm → TransDeep → WitComp → WitForget → WitDeep := by
  intro _ hSm hTD hWC hWF p _ D G L R _ _ gb X N' N h hI
  obtain ⟨k, hk, hAk, hex⟩ := hTD p D G L R gb h hI
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact absurd (Nat.coprime_zero_left _ |>.mp hk) (Fact.out : p.Prime).one_lt.ne'
    · exact hpos
  let Nk : Lv p := ⟨↑N * k, le_trans N.2.1 (Nat.le_mul_of_pos_right _ hk0), Nat.Coprime.mul_left N.2.2 hk⟩
  let M : Lv p := ⟨↑N' * (↑N * k), le_trans Nk.2.1 (Nat.le_mul_of_pos_left _ (by have := N'.2.1; omega)),
    Nat.Coprime.mul_left N'.2.2 Nk.2.2⟩
  have hNkM : (↑Nk : ℕ) ∣ ↑M := Dvd.intro_left _ rfl
  refine ⟨M, Dvd.intro _ rfl, ?_, ?_⟩
  · intro u hu
    exact hAk N u (UpperTheory.Gal.Int.Geo.KN_anti hNkM hu)
  · haveI : Smooth (X Nk).s := (hSm p D R gb Nk (X Nk)).1
    haveI : IsLocallyNoetherian (X Nk).X := LocallyOfFiniteType.isLocallyNoetherian (X Nk).s
    obtain ⟨o, ψ, ht⟩ := hex N (X Nk).X (X Nk).s (X Nk).univ
    obtain ⟨π, ⟨hπ, ⟨φ⟩⟩, -⟩ := (X N).rep (X Nk).X (X Nk).s o
    have w₂ : Wit L h (X Nk) (X N) π (ψ.left ≫ φ.φ) := ⟨hπ, o, ψ, φ, ht, rfl⟩
    obtain ⟨c, Φc, w₁, -⟩ := hWF p D G L R gb Nk M hNkM (X Nk) (X M)
    have := (hWC p D G L R gb M Nk N (X M) (X Nk) (X N) 1 h).2 hI (hAk N) c Φc π _ w₁ w₂
    rw [_root_.mul_one] at this
    exact ⟨_, _, this⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitEx
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u


open GlobalTheory.UPel.HT.Hecke in
private theorem gObjMap_comp_keep {G₀ : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G₀ R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂}
    {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : GObjMap o₁ o₂ f) (h₂ : GObjMap o₂ o₃ g) :
    ∃ m : GObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have e₁ : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have e₂ : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ => h₂.φ₂) (fun _ => 1) h₁.φ₂) e₁
  refine ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, ?_, ?_,
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol e₂, ?_⟩, rfl⟩
  · exact ⟨by simp only [Category.assoc, h₂.sq.1, reassoc_of% h₁.sq.1],
      by simp only [Category.assoc, h₂.sq.2, reassoc_of% h₁.sq.2]⟩
  · intro c
    simp only [← Category.assoc, h₁.act c]
    simp only [Category.assoc, h₂.act c]
  · intro y
    simp only [reassoc_of% h₁.eta y, h₂.eta y, Category.assoc]

theorem UpperTheory.Gal.G3.pWitEx :
    KNBasic → GenSm → Rigid → WitForget → WitDeep → DescMap → TransIso → TransCancel → TransDesc → WitEx := by
  intro _ hSm hRig hWF hWD hDM hTI hTC hTD p _ D G L R _ _ gb X N' N h hI hA
  obtain ⟨M, hdiv, hAM, π₁, Φ₁, hs₁, o₁, ψ₁, φ₁, ht₁, hΦ₁⟩ := hWD p D G L R gb X N' N h hI
  obtain ⟨c, Φc, hw, hfin, het, hsur⟩ := hWF p D G L R gb N' M hdiv (X N') (X M)
  have hA1 : AdmK L (↑M) (↑N') 1 := by
    intro u hu
    simpa using UpperTheory.Gal.Int.Geo.KN_anti hdiv hu
  obtain ⟨π, Φ, hcπ, hΦ, hπs, hΦw⟩ :=
    hDM p D G L R gb M N' N (X M) (X N') (X N) h hI hA hA1 c Φc π₁ Φ₁ hw hfin het hsur
      ⟨hs₁, o₁, ψ₁, φ₁, ht₁, hΦ₁⟩
  subst hcπ
  obtain ⟨hsc, oc, ψc, φc, htc, hΦc⟩ := hw
  obtain ⟨o, ⟨φ⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (X N').s π hπs (X N).univ
  let ψl : (X N').univ.A.left ⟶ o.A.left :=
    φ.cart.1.lift Φ (X N').univ.A.hom hΦw
  have hψ₁ : ψl ≫ φ.φ = Φ := φ.cart.1.lift_fst _ _ _
  have hψ₂ : ψl ≫ o.A.hom = (X N').univ.A.hom := φ.cart.1.lift_snd _ _ _
  let ψ : (X N').univ.A ⟶ o.A := Over.homMk ψl hψ₂
  refine ⟨π, Φ, hπs, o, ψ, φ, ?_, hψ₁.symm⟩
  obtain ⟨m₂⟩ := BaseChange.gObjMap_cancel φ₁ φ
  haveI := hTI p D G L R gb (X M).X (X M).s M N' (X M).univ oc ψc 1 (one_mem _) htc
  have htr : IsTrans L h oc o₁ (inv ψc ≫ ψ₁) :=
    hTC p D G L R gb (X M).X (X M).s M N' N (X M).univ oc o₁ ψc (inv ψc ≫ ψ₁) h hI hAM htc
      (by simpa using ht₁)
  haveI : Smooth (X M).s := (hSm p D R gb M (X M)).1
  haveI : AlgebraicGeometry.IsReduced (X M).X := GlobalTheory.isReduced_of_smooth_of_isReduced (X M).s
  have hcomp : m₂.φ ≫ φ.φ = φ₁.φ := by
    obtain ⟨m, hm⟩ := gObjMap_comp_keep m₂ φ
    rw [← hm]
    exact hRig p D R gb (X N).X (X M).X (X N).s (X M).s (c ≫ π)
      (by rw [Category.assoc, hπs, hsc]) N (X N).univ o₁ m φ₁
  refine hTD p D G L R gb (X N').X (X M).X (X N').s (X M).s c hsc N' N (X N').univ o oc o₁ φc m₂ ψ
    (inv ψc ≫ ψ₁) h ?_ htr
  have key : ψc.left ≫ φc.φ ≫ Φ = ψ₁.left ≫ φ₁.φ := by
    rw [← Category.assoc, ← hΦc, hΦ, hΦ₁]
  apply φ.cart.1.hom_ext
  · simp only [Category.assoc, hcomp, ψ, Over.homMk_left, hψ₁, Over.comp_left]
    rw [← key, ← Category.assoc, ← Over.comp_left, IsIso.inv_hom_id, Over.id_left, Category.id_comp]
  · simp only [Category.assoc, ψ, Over.homMk_left, hψ₂, Over.comp_left]
    rw [m₂.cart.1.w, φc.cart.1.w, ← Over.comp_left_assoc, Over.w_assoc]
end

