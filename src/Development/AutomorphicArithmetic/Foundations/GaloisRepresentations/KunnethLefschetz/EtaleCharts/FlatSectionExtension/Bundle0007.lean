module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatExists
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

namespace UpperTheory.Gal.KunnethLefschetz.G.PX

variable {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
  {D : E.LineData Y} {d : ℕ}

private theorem wI_cP (B : Blow q i π D d) (α : B.ι) : wI B α ≫ cP B = (oW B α).ι := by
  unfold wI cP
  exact Sigma.ι_desc _ _

private theorem mem_V (B : Blow q i π D d) {U : Scheme.{0}} {p : U ⟶ W} {α : B.ι}
    (c : U ⟶ (oW B α : Scheme.{0})) (h : p = c ≫ (oW B α).ι) (y : U) : (p ≫ i) y ∈ B.V α := by
  subst h
  have h₁ : (c y).1 ∈ oW B α := (c y).2
  have h₂ : i (c y).1 ∈ B.V α := h₁
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact h₂

private theorem exists_loc (B : Blow q i π D d) {V : Scheme.{0}} (a b : V ⟶ WP B)
    (h : a ≫ cP B = b ≫ cP B) (x : V) :
    ∃ (U : V.Opens) (α β : B.ι) (a₁ : (U : Scheme.{0}) ⟶ oW B α) (b₁ : (U : Scheme.{0}) ⟶ oW B β)
      (M : Matrix (Fin d) (Fin d) Γ((U : Scheme.{0}), ⊤)), x ∈ U ∧
      U.ι ≫ a = a₁ ≫ wI B α ∧ U.ι ≫ b = b₁ ≫ wI B β ∧ LocMat B α β (U.ι ≫ a ≫ cP B) M := by
  obtain ⟨U₁, α, a₀, hx₁, ha⟩ := sigmaLocal (fun α : B.ι => (oW B α : Scheme.{0})) a x
  obtain ⟨U₂, β, b₀, hx₂, hb⟩ := sigmaLocal (fun α : B.ι => (oW B α : Scheme.{0})) b x
  have ha' : (U₁ ⊓ U₂).ι ≫ a = (V.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≫ a₀) ≫ wI B α := by
    have ha₀ : U₁.ι ≫ a = a₀ ≫ wI B α := ha
    rw [Category.assoc, ← ha₀, ← Category.assoc, Scheme.homOfLE_ι]
  have hb' : (U₁ ⊓ U₂).ι ≫ b = (V.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂) ≫ b₀) ≫ wI B β := by
    have hb₀ : U₂.ι ≫ b = b₀ ≫ wI B β := hb
    rw [Category.assoc, ← hb₀, ← Category.assoc, Scheme.homOfLE_ι]
  have e₁ : (U₁ ⊓ U₂).ι ≫ a ≫ cP B = (V.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≫ a₀) ≫ (oW B α).ι := by
    rw [← Category.assoc, ha', Category.assoc, wI_cP]
  have e₂ : (U₁ ⊓ U₂).ι ≫ a ≫ cP B = (V.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂) ≫ b₀) ≫ (oW B β).ι := by
    rw [h, ← Category.assoc, hb', Category.assoc, wI_cP]
  obtain ⟨M, hM⟩ := locMatExists B α β ((U₁ ⊓ U₂).ι ≫ a ≫ cP B)
    (fun y => ⟨mem_V B _ e₁ y, mem_V B _ e₂ y⟩)
  exact ⟨U₁ ⊓ U₂, α, β, _, _, M, ⟨hx₁, hx₂⟩, ha', hb', hM⟩

private theorem compat (B : Blow q i π D d) {V S : Scheme.{0}} (a b : V ⟶ WP B) {U U' : V.Opens}
    (f : S ⟶ (U : Scheme.{0})) (f' : S ⟶ (U' : Scheme.{0})) (e : f ≫ U.ι = f' ≫ U'.ι)
    {α β α' β' : B.ι} (a₁ : (U : Scheme.{0}) ⟶ oW B α) (b₁ : (U : Scheme.{0}) ⟶ oW B β)
    (a₁' : (U' : Scheme.{0}) ⟶ oW B α') (b₁' : (U' : Scheme.{0}) ⟶ oW B β')
    (ha : U.ι ≫ a = a₁ ≫ wI B α) (hb : U.ι ≫ b = b₁ ≫ wI B β)
    (ha' : U'.ι ≫ a = a₁' ≫ wI B α') (hb' : U'.ι ≫ b = b₁' ≫ wI B β')
    (M : Matrix (Fin d) (Fin d) Γ((U : Scheme.{0}), ⊤)) (M' : Matrix (Fin d) (Fin d) Γ((U' : Scheme.{0}), ⊤))
    (hM : LocMat B α β (U.ι ≫ a ≫ cP B) M) (hM' : LocMat B α' β' (U'.ι ≫ a ≫ cP B) M') :
    M.map f.appTop.hom = M'.map f'.appTop.hom := by
  by_cases hS : Nonempty S
  · obtain ⟨s⟩ := hS
    have ea : (f ≫ a₁) ≫ wI B α = (f' ≫ a₁') ≫ wI B α' := by
      rw [Category.assoc, Category.assoc, ← ha, ← ha', ← Category.assoc, ← Category.assoc, e]
    have eb : (f ≫ b₁) ≫ wI B β = (f' ≫ b₁') ≫ wI B β' := by
      rw [Category.assoc, Category.assoc, ← hb, ← hb', ← Category.assoc, ← Category.assoc, e]
    obtain rfl : α = α' := sigmaDisj (fun α : B.ι => (oW B α : Scheme.{0})) _ _ s ea
    obtain rfl : β = β' := sigmaDisj (fun α : B.ι => (oW B α : Scheme.{0})) _ _ s eb
    have n₁ := locMatNat B α β f _ M hM
    have n₂ := locMatNat B α β f' _ M' hM'
    have ep : f ≫ U.ι ≫ a ≫ cP B = f' ≫ U'.ι ≫ a ≫ cP B := by
      rw [← Category.assoc, e, Category.assoc]
    rw [ep] at n₁
    exact locMatUnique B α β _ _ _ n₁ n₂
  · have : IsEmpty S := not_nonempty_iff.mp hS
    ext r c
    exact sectionExt _ _ (fun x => isEmptyElim x)

end UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gMatExists :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V : Scheme.{0}} (a b : V ⟶ WP B), a ≫ cP B = b ≫ cP B → ∃ M : Matrix (Fin d) (Fin d) Γ(V, ⊤), GMat B a b M := by
  intro K _ W Z Y q i π D d B V a b h
  choose U α β a₁ b₁ M hx ha hb hM using exists_loc B a b h
  have hg : ∀ r c, ∃ s₀ : Γ(V, ⊤), ∀ x, (U x).ι.appTop.hom s₀ = M x r c := fun r c =>
    glueSection U hx (fun x => M x r c) (fun x y S f f' e => by
      have h₁ := compat B a b f f' e (a₁ x) (b₁ x) (a₁ y) (b₁ y) (ha x) (hb x) (ha y) (hb y)
        (M x) (M y) (hM x) (hM y)
      exact congrFun (congrFun h₁ r) c)
  choose G hG using hg
  refine ⟨Matrix.of G, fun x => ⟨U x, α x, β x, a₁ x, b₁ x, hx x, ha x, hb x, ?_⟩⟩
  have e : (Matrix.of G).map (U x).ι.appTop.hom = M x := by
    ext r c
    exact hG r c x
  rw [e]
  exact hM x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GvField
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem uV_eq' {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V : Scheme.{0}} {y y' : V ⟶ Y}
    (e : y = y') (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (h' : ⊤ ≤ y' ⁻¹ᵁ (B.c α).C k) : uV B α k y h = uV B α k y' h' := by
  subst e; rfl

private theorem secOf_eq' {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V : Scheme.{0}} {y y' : V ⟶ Y}
    (e : y = y') (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (h' : ⊤ ≤ y' ⁻¹ᵁ (B.c α).C k) : secOf B α k y h = secOf B α k y' h' := by
  subst e; rfl

private theorem u_eq' {Y : Scheme.{0}} (D : E.LineData Y) {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y}
    (ea : a = a') (eb : b = b') (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) : D.u a b h = D.u a' b' h' := by
  subst ea eb; rfl

private theorem rho_c {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W)
    (hw : j ≫ π = r ≫ i) : rhoP B j r hw ≫ cP B = eP B j ≫ r := by
  refine Sigma.hom_ext _ _ fun p => ?_
  simp only [rhoP, cP, eP, wI, Category.assoc, colimit.ι_desc_assoc, colimit.ι_desc, Cofan.mk_ι_app, Discrete.functor_obj_eq_as,
    rhoC, IsOpenImmersion.lift_fac]

private theorem core {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W)
    (hsq : IsPullback j r π i) (v : Fin d → Γ(TP B j, ⊤)) (hv : IsV B j v) {V : Scheme.{0}}
    (p p' : B.ι × Fin d) (a₁ : V ⟶ (oT B j p : Scheme.{0})) (b₁ : V ⟶ (oT B j p' : Scheme.{0}))
    (hab : (a₁ ≫ tI B j p) ≫ eP B j = (b₁ ≫ tI B j p') ≫ eP B j)
    (hh : ((a₁ ≫ tI B j p) ≫ tauP B j) ≫ D.f = ((b₁ ≫ tI B j p') ≫ tauP B j) ≫ D.f)
    (M : Matrix (Fin d) (Fin d) Γ(V, ⊤))
    (hG : GMat B ((a₁ ≫ tI B j p) ≫ rhoP B j r hsq.w) ((b₁ ≫ tI B j p') ≫ rhoP B j r hsq.w) M) :
    M.mulVec ((a₁ ≫ tI B j p).appTop.hom ∘ v) =
      (((D.u _ _ hh)⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) • ((b₁ ≫ tI B j p').appTop.hom ∘ v) := by
  obtain ⟨h₁, e1, e2, e3⟩ := UpperTheory.Gal.KunnethLefschetz.G.PX.pieceFacts B j r hsq.w v hv p a₁
  obtain ⟨h₂, f1, f2, f3⟩ := UpperTheory.Gal.KunnethLefschetz.G.PX.pieceFacts B j r hsq.w v hv p' b₁
  have hy : (b₁ ≫ tI B j p') ≫ eP B j ≫ j = (a₁ ≫ tI B j p) ≫ eP B j ≫ j := by
    rw [← Category.assoc, ← hab, Category.assoc]
  have h₂' : ⊤ ≤ ((a₁ ≫ tI B j p) ≫ eP B j ≫ j) ⁻¹ᵁ (B.c p'.1).C p'.2 := hy ▸ h₂
  have hL := UpperTheory.Gal.KunnethLefschetz.G.PX.gMatLoc B _ _ M p.1 p'.1 (a₁ ≫ rhoC B j r hsq.w p) (b₁ ≫ rhoC B j r hsq.w p') e3 f3 hG
  have hc : ((a₁ ≫ tI B j p) ≫ eP B j ≫ j) ≫ π = (((a₁ ≫ tI B j p) ≫ rhoP B j r hsq.w) ≫ cP B) ≫ i := by
    rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, Category.assoc, hsq.w,
      ← Category.assoc (rhoP B j r hsq.w), rho_c B j r hsq.w]
    simp only [Category.assoc]
  have key := UpperTheory.Gal.KunnethLefschetz.G.PX.gvChart B _ _ hc p.1 p'.1 p.2 p'.2 h₁ h₂' M hL
  rw [e1, f1, uV_eq' B p'.1 p'.2 hy h₂ h₂',
    u_eq' D e2 (f2.trans (secOf_eq' B p'.1 p'.2 hy h₂ h₂')) hh
      ((secOf_f B p.1 p.2 _ h₁).trans (secOf_f B p'.1 p'.2 _ h₂').symm)]
  exact key

private theorem core' {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W)
    (hsq : IsPullback j r π i) (v : Fin d → Γ(TP B j, ⊤)) (hv : IsV B j v) {V : Scheme.{0}}
    (p p' : B.ι × Fin d) (a₁ : V ⟶ (oT B j p : Scheme.{0})) (b₁ : V ⟶ (oT B j p' : Scheme.{0}))
    (a b : V ⟶ TP B j) (ea : a = a₁ ≫ tI B j p) (eb : b = b₁ ≫ tI B j p')
    (hab : a ≫ eP B j = b ≫ eP B j) (hh : (a ≫ tauP B j) ≫ D.f = (b ≫ tauP B j) ≫ D.f)
    (M : Matrix (Fin d) (Fin d) Γ(V, ⊤))
    (hG : GMat B (a ≫ rhoP B j r hsq.w) (b ≫ rhoP B j r hsq.w) M) :
    M.mulVec (a.appTop.hom ∘ v) = (((D.u _ _ hh)⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) • (b.appTop.hom ∘ v) := by
  subst ea eb
  exact core B j r hsq v hv p p' a₁ b₁ hab hh M hG

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gvField :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W) (hsq : IsPullback j r π i) (v : Fin d → Γ(TP B j, ⊤)), IsV B j v → ∀ {V : Scheme.{0}} (a b : V ⟶ TP B j), a ≫ eP B j = b ≫ eP B j → ∀ (hh : (a ≫ tauP B j) ≫ D.f = (b ≫ tauP B j) ≫ D.f) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)), GMat B (a ≫ rhoP B j r hsq.w) (b ≫ rhoP B j r hsq.w) M → M.mulVec (a.appTop.hom ∘ v) = (((D.u _ _ hh)⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) • (b.appTop.hom ∘ v) := by
  intro K _ W Z Y q i π D d B T j r hsq v hv V a b hab hh M hG
  funext m
  refine UpperTheory.Gal.KunnethLefschetz.G.PX.sectionExt _ _ fun x => ?_
  obtain ⟨U₁, p, a₁, hx₁, ha⟩ := UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaLocal (fun p : B.ι × Fin d => (oT B j p : Scheme.{0})) a x
  obtain ⟨U₂, p', b₁, hx₂, hb⟩ := UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaLocal (fun p : B.ι × Fin d => (oT B j p : Scheme.{0})) b x
  let U : V.Opens := U₁ ⊓ U₂
  have hU₁ : U ≤ U₁ := inf_le_left
  have hU₂ : U ≤ U₂ := inf_le_right
  have ea : U.ι ≫ a = (V.homOfLE hU₁ ≫ a₁) ≫ tI B j p := by
    have : (V.homOfLE hU₁ ≫ a₁) ≫ tI B j p = V.homOfLE hU₁ ≫ (U₁.ι ≫ a) := by
      rw [ha]; simp [tI]
    rw [this, ← Category.assoc, Scheme.homOfLE_ι]
  have eb : U.ι ≫ b = (V.homOfLE hU₂ ≫ b₁) ≫ tI B j p' := by
    have : (V.homOfLE hU₂ ≫ b₁) ≫ tI B j p' = V.homOfLE hU₂ ≫ (U₂.ι ≫ b) := by
      rw [hb]; simp [tI]
    rw [this, ← Category.assoc, Scheme.homOfLE_ι]
  refine ⟨U, ⟨hx₁, hx₂⟩, ?_⟩
  have hG' : GMat B ((U.ι ≫ a) ≫ rhoP B j r hsq.w) ((U.ι ≫ b) ≫ rhoP B j r hsq.w) (M.map U.ι.appTop.hom) := by
    simpa only [Category.assoc] using UpperTheory.Gal.KunnethLefschetz.G.PX.gMatNat B U.ι _ _ M hG
  have hab' : (U.ι ≫ a) ≫ eP B j = (U.ι ≫ b) ≫ eP B j := by
    rw [Category.assoc, Category.assoc, hab]
  have hh' : ((U.ι ≫ a) ≫ tauP B j) ≫ D.f = ((U.ι ≫ b) ≫ tauP B j) ≫ D.f := by
    simp only [Category.assoc] at hh ⊢
    rw [hh]
  have res := core' B j r hsq v hv p p' _ _ (U.ι ≫ a) (U.ι ≫ b) ea eb hab' hh' _ hG'
  have hc : ∀ g : V ⟶ TP B j, (U.ι ≫ g).appTop.hom ∘ v = U.ι.appTop.hom ∘ (g.appTop.hom ∘ v) := by
    intro g
    funext l
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, Scheme.Hom.comp_appTop]
    rfl
  have hu : D.u ((U.ι ≫ a) ≫ tauP B j) ((U.ι ≫ b) ≫ tauP B j) hh' =
      Units.map U.ι.appTop.hom.toMonoidHom (D.u _ _ hh) := by
    rw [← D.nat]
    exact u_eq' D (Category.assoc _ _ _) (Category.assoc _ _ _) _ _
  rw [hc a, hc b, hu] at res
  have e := congrFun res m
  rw [RingHom.map_mulVec, e]
  simp [Pi.smul_apply, smul_eq_mul, map_mul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.RatioInj
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem mem_of_unit {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (β : B.ι) (m l : Fin d) {V : Scheme.{0}} (y : V ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ (B.c β).C m) (hu : IsUnit (uV B β m y h l)) : ⊤ ≤ y ⁻¹ᵁ (B.c β).C l := by
  have h1 : V.basicOpen (uV B β m y h l) = ⊤ := Scheme.basicOpen_of_isUnit V hu
  have h2 : V.basicOpen (uV B β m y h l) ≤ y ⁻¹ᵁ (Y.basicOpen ((B.c β).u m l)) := by
    unfold uV
    rw [Scheme.Hom.appLE]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    rw [Scheme.basicOpen_res, Scheme.preimage_basicOpen]
    exact inf_le_right
  intro x hx
  have h3 : x ∈ y ⁻¹ᵁ (Y.basicOpen ((B.c β).u m l)) := h2 (h1.ge hx)
  have h4 : y x ∈ Y.basicOpen ((B.c β).u m l) := h3
  rw [← (B.c β).inter m l] at h4
  exact h4.2

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.ratioInj :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (β : B.ι) (m l : Fin d) {V : Scheme.{0}} (y y' : V ⟶ Y) (p : V ⟶ W) (h : ⊤ ≤ y ⁻¹ᵁ (B.c β).C m) (h' : ⊤ ≤ y' ⁻¹ᵁ (B.c β).C l) (s : (Γ(V, ⊤))ˣ), y ≫ π = p ≫ i → y' ≫ π = p ≫ i → uV B β m y h = (s : Γ(V, ⊤)) • uV B β l y' h' → y = y' := by
  intro K _ W Z Y q i π D d B β m l V y y' p h h' s hy hy' e
  have hl : uV B β m y h l = (s : Γ(V, ⊤)) := by
    have := congrFun e l
    simpa [uSelf B β l y' h'] using this
  have h'' : ⊤ ≤ y ⁻¹ᵁ (B.c β).C l := mem_of_unit B β m l y h (hl ▸ s.isUnit)
  have hV : ∀ x : V, (p ≫ i) x ∈ B.V β := by
    intro x
    rw [← hy, Scheme.Hom.comp_apply]
    exact (B.c β).C_le m (h (Set.mem_univ x))
  have hg := gvChart B y p hy β β m l h h'' 1 (locMatOne B β p hV)
  rw [Matrix.one_mulVec] at hg
  obtain ⟨c, hc⟩ : ∃ c : (Γ(V, ⊤))ˣ, uV B β m y h = (c : Γ(V, ⊤)) • uV B β l y h'' := ⟨_, hg⟩
  have hcs : (c : Γ(V, ⊤)) = s := by
    have := congrFun hc l
    rw [hl, Pi.smul_apply, uSelf B β l y h'', smul_eq_mul, mul_one] at this
    exact this.symm
  have hvv : uV B β l y h'' = uV B β l y' h' := by
    funext j
    have h1 := congrFun hc j
    have h2 := congrFun e j
    rw [Pi.smul_apply, smul_eq_mul] at h1 h2
    rw [hcs] at h1
    exact s.isUnit.mul_left_cancel (h1.symm.trans h2)
  exact chartInj B β l y y' h'' h' (hy.trans hy'.symm) hvv
end

