module

public import Development.EtaleCohomology.TateTwists.Bundle0019
public import Development.EtaleCohomology.TateTwists.Bundle0002
public import Development.EtaleCohomology.TateTwists.Bundle0003
public import Development.EtaleCohomology.TateTwists.Bundle0001

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistQuotientOfLocalCriterionAn
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

noncomputable def muK (q : ℕ) (A : CommRingCat.{0}) : Submodule (ULift.{1} (ZMod q)) ((twF q 1).obj A) :=
  Submodule.span _ {x | ∃ l : List (Prim q A), (l.map fun ζ => ζ.1).prod = 1 ∧
    x = (l.map fun ζ => twGenR A ζ).sum}

theorem muK_gen_map (q : ℕ) {A B : CommRingCat.{0}} (f : A ⟶ B) (ζ : Prim q A) :
    ((twF q 1).map f).hom (twGenR A ζ) = twGenR B (ζ.map f.hom) := by
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) (Finsupp.single ζ 1)) = _
  rw [Finsupp.mapDomain_single]
  rfl

theorem muK_le (q : ℕ) {A B : CommRingCat.{0}} (f : A ⟶ B) :
    muK q A ≤ (muK q B).comap ((twF q 1).map f).hom := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨l, hl, rfl⟩
  refine Submodule.subset_span ⟨l.map (Prim.map f.hom), ?_, ?_⟩
  · have : ((l.map fun ζ => ζ.1).map f.hom).prod = f.hom 1 := by rw [← map_list_prod, hl]
    rw [map_one] at this
    rw [← this, List.map_map, List.map_map]
    rfl
  · rw [map_list_sum, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro ζ _
    exact muK_gen_map q f ζ

noncomputable def muT (q : ℕ) : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) where
  obj A := ModuleCat.of _ ((twF q 1).obj A ⧸ muK q A)
  map f := ModuleCat.ofHom (Submodule.mapQ _ _ ((twF q 1).map f).hom (muK_le q f))
  map_id A := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_))
    change Submodule.Quotient.mk (((twF q 1).map (𝟙 A)).hom x) = Submodule.Quotient.mk x
    rw [(twF q 1).map_id]; rfl
  map_comp f g := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_))
    change Submodule.Quotient.mk (((twF q 1).map (f ≫ g)).hom x) =
      Submodule.Quotient.mk (((twF q 1).map g).hom (((twF q 1).map f).hom x))
    rw [(twF q 1).map_comp]; rfl

noncomputable def muτ (q : ℕ) : twF q 1 ⟶ muT q where
  app A := ModuleCat.ofHom (muK q A).mkQ
  naturality A B f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    rfl

theorem muτ_list (q : ℕ) (A : CommRingCat.{0}) (l : List (Prim q A)) (hl : (l.map fun ζ => ζ.1).prod = 1) :
    (l.map fun ζ => ((muτ q).app A).hom (twGenR A ζ)).sum = 0 := by
  have h : (l.map fun ζ => twGenR A ζ).sum ∈ muK q A := Submodule.subset_span ⟨l, hl, rfl⟩
  have := (Submodule.Quotient.mk_eq_zero (muK q A)).2 h
  refine Eq.trans ?_ this
  change _ = ((muτ q).app A).hom (List.map (fun ζ => twGenR A ζ) l).sum
  rw [map_list_sum, List.map_map]
  rfl

def EtaleSheafifyMonoOfKernelLocallyZeroCriterion : Prop :=
  ∀ (q : ℕ) (P Q : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (τ : P ⟶ Q),
    (∀ (U : Scheme.{0}) (x : P.obj Γ(U, ⊤)), (τ.app _).hom x = 0 → Loc U fun _ g => (P.map g.appTop).hom x = 0) →
    Mono ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ))

def MuRootRelationSubmoduleEtaleLocallyZero : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (x : (twF q 1).obj Γ(U, ⊤)), x ∈ muK q Γ(U, ⊤) →
    Loc U fun _ g => ((twF q 1).map g.appTop).hom x = 0

theorem etale_sheafify_mono_of_kernel_locally_zero : EtaleSheafifyMonoOfKernelLocallyZeroCriterion := by
  intro q P Q τ h
  have hli : Presheaf.IsLocallyInjective Scheme.etaleTopology (Functor.whiskerLeft Scheme.Γ τ) := by
    refine ⟨fun {X} x y hxy => ?_⟩
    let x' : P.obj Γ(X.unop, ⊤) := x
    let y' : P.obj Γ(X.unop, ⊤) := y
    have hxy' : (τ.app _).hom x' = (τ.app _).hom y' := hxy
    obtain ⟨S, hS, hSP⟩ := h X.unop (x' - y') (by rw [map_sub, hxy', sub_self])
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V g hg
    have h2 : (P.map g.appTop).hom (x' - y') = 0 := hSP V g hg
    rw [map_sub, sub_eq_zero] at h2
    exact h2
  have : Sheaf.IsLocallyInjective ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ)) :=
    (Presheaf.isLocallyInjective_presheafToSheaf_map_iff _ _).2 hli
  exact Sheaf.mono_of_isLocallyInjective _

theorem exists_etale_mono_muTwist_quotient_of_locally_zero (h1 : EtaleSheafifyMonoOfKernelLocallyZeroCriterion) (h2 : MuRootRelationSubmoduleEtaleLocallyZero) :
    ExistsEtaleMonoMuTwistKillingRootRelations := by
  intro q _
  refine ⟨muT q, muτ q, h1 q _ _ (muτ q) fun U x hx => h2 q U x ?_, muτ_list q⟩
  exact (Submodule.Quotient.mk_eq_zero (muK q _)).1 hx

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.KumMulCocPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.KMC

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_bind {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hb : ∀ V (g : V ⟶ U), P V g → Loc V (fun W k => Q W (k ≫ g))) : Loc U Q := by
  classical
  obtain ⟨S, hS, hP⟩ := h
  choose R hR hQ using fun V (g : V ⟶ U) (hg : S.arrows g) => hb V g (hP V g hg)
  refine ⟨Sieve.bind S.arrows (fun V g hg => R V g hg),
    Scheme.etaleTopology.bind_covering hS (fun V g hg => hR V g hg), ?_⟩
  rintro W h ⟨V, k, g, hg, hk, rfl⟩
  exact hQ V g hg W k hk

theorem umap_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : (Γ(U, ⊤))ˣ) :
    Units.map (k ≫ g).appTop.hom.toMonoidHom a =
      Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom a) := by
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rfl

theorem unit_q {V U : Scheme.{0}} (q : ℕ) (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤))) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using hq.map g.appTop.hom

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (s : Sec F U) :
    Sec.res k (Sec.res g s) = Sec.res (k ≫ g) s := by
  simp [Sec.res]

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (s : Sec F U) :
    Sec.res g (Sec.map φ s) = Sec.map φ (Sec.res g s) := by
  simp only [Sec.res, Sec.map]
  exact congrArg (fun f => f.hom s) (φ.hom.naturality g.op).symm

variable (q : ℕ)

theorem kumT_pow (hk : IsKum q (kumT q)) {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤)) :
    ∀ (n : ℕ) (v w : (Γ(V, ⊤))ˣ), (w : Γ(V, ⊤)) = ζ.1 ^ n * v → kumT q V w = kumT q V v + n • resGen 1 ζ := by
  intro n
  induction n with
  | zero => intro v w h; simp at h; rw [Units.ext h]; simp
  | succ n ih =>
    intro v w h
    have hu : IsUnit (ζ.1 ^ n * v) := by
      apply isUnit_of_mul_isUnit_right (x := ζ.1); rw [← mul_assoc, ← pow_succ']; rw [← h]; exact w.isUnit
    rw [hk.2 V ζ hu.unit w (by rw [h, hu.unit_spec, pow_succ', mul_assoc]), ih v hu.unit hu.unit_spec]
    rw [succ_nsmul]; abel

noncomputable def D (V : Scheme.{0}) (a b : (Γ(V, ⊤))ˣ) : Sec ((res _ (tw q 1)).X 0) V :=
  kumT q V (a * b) - kumT q V a - kumT q V b

theorem D_comm (V : Scheme.{0}) (a b : (Γ(V, ⊤))ˣ) : D q V a b = D q V b a := by
  simp only [D, mul_comm a b]; abel

theorem D_res (hk : IsKum q (kumT q)) {W V : Scheme.{0}} (k : W ⟶ V) (hq : IsUnit (q : Γ(V, ⊤))) (a b : (Γ(V, ⊤))ˣ) :
    Sec.res k (D q V a b) = D q W (Units.map k.appTop.hom.toMonoidHom a) (Units.map k.appTop.hom.toMonoidHom b) := by
  simp only [D, Sec.res, map_sub] at *
  have h := hk.1 W V k
  simp only [Sec.res] at h
  rw [h _ hq, h _ hq, h _ hq, map_mul]

theorem D_change (hk : IsKum q (kumT q)) (hp : EtalePrimitiveRootsExistLocally) (hs : EtaleSheafSectionsSeparatedAndGlue) [NeZero q]
    {V : Scheme.{0}} (hq : IsUnit (q : Γ(V, ⊤))) (a a' b : (Γ(V, ⊤))ˣ) (h : a' ^ q = a ^ q) :
    D q V a' b = D q V a b := by
  apply (hs _ _ V).1
  set c := a' * a⁻¹ with hcdef
  have hc : c ^ q = 1 := by rw [hcdef, mul_pow, h, inv_pow, mul_inv_cancel]
  have hac : a' = c * a := by rw [hcdef, inv_mul_cancel_right]
  refine loc_bind ((hp q V).1 hq) (fun W g hζ => ?_)
  obtain ⟨ζ⟩ := hζ
  refine loc_mono ((hp q W).2.2.1 ζ (g.appTop.hom c) (by rw [← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one])) (fun W' k hn => ?_)
  obtain ⟨n, hn⟩ := hn
  have hq' : IsUnit (q : Γ(V, ⊤)) := hq
  rw [D_res q hk (k ≫ g) hq, D_res q hk (k ≫ g) hq]
  simp only [umap_comp]
  set ζ'' : Prim q Γ(W', ⊤) := Prim.map k.appTop.hom ζ
  set A := Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom a)
  set A' := Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom a')
  set B := Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom b)
  have key : (A' : Γ(W', ⊤)) = ζ''.1 ^ n * A := by
    simp only [A, A', ζ'', Prim.map, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, hac,
      Units.val_mul, map_mul]
    rw [hn]
  unfold D
  rw [kumT_pow q hk ζ'' n (A * B) (A' * B) (by rw [Units.val_mul, Units.val_mul, key, mul_assoc]),
    kumT_pow q hk ζ'' n A A' key]
  abel

theorem D_change2 (hk : IsKum q (kumT q)) (hp : EtalePrimitiveRootsExistLocally) (hs : EtaleSheafSectionsSeparatedAndGlue) [NeZero q]
    {V : Scheme.{0}} (hq : IsUnit (q : Γ(V, ⊤))) (a a' b b' : (Γ(V, ⊤))ˣ) (ha : a' ^ q = a ^ q) (hb : b' ^ q = b ^ q) :
    D q V a' b' = D q V a b := by
  rw [D_change q hk hp hs hq a a' b' ha, D_comm, D_change q hk hp hs hq b b' a hb, D_comm]

def KP {V : Scheme.{0}} (u v : (Γ(V, ⊤))ˣ) (Z : Sec ((res _ (tw q 1)).X 0) V) : Prop :=
  ∀ (W : Scheme.{0}) (k : W ⟶ V) (a b : (Γ(W, ⊤))ˣ), a ^ q = Units.map k.appTop.hom.toMonoidHom u →
    b ^ q = Units.map k.appTop.hom.toMonoidHom v → Sec.res k Z = D q W a b

theorem KP_res {W V : Scheme.{0}} (k : W ⟶ V) {u v : (Γ(V, ⊤))ˣ} {Z : Sec ((res _ (tw q 1)).X 0) V}
    (hZ : KP q u v Z) : KP q (Units.map k.appTop.hom.toMonoidHom u) (Units.map k.appTop.hom.toMonoidHom v) (Sec.res k Z) := by
  intro W' k' a b ha hb
  rw [res_comp]
  exact hZ W' (k' ≫ k) a b (by rw [ha, umap_comp]) (by rw [hb, umap_comp])

theorem KP_uniq (hp : EtalePrimitiveRootsExistLocally) (hs : EtaleSheafSectionsSeparatedAndGlue) [NeZero q]
    {V : Scheme.{0}} (hq : IsUnit (q : Γ(V, ⊤))) {u v : (Γ(V, ⊤))ˣ} {Z₁ Z₂ : Sec ((res _ (tw q 1)).X 0) V}
    (h₁ : KP q u v Z₁) (h₂ : KP q u v Z₂) : Z₁ = Z₂ := by
  apply (hs _ _ V).1
  refine loc_bind ((hp q V).2.2.2 hq u) (fun W g ha => ?_)
  obtain ⟨a, ha⟩ := ha
  refine loc_mono ((hp q W).2.2.2 (unit_q q g hq) (Units.map g.appTop.hom.toMonoidHom v)) (fun W' k hb => ?_)
  obtain ⟨b, hb⟩ := hb
  have ha' : (Units.map k.appTop.hom.toMonoidHom a) ^ q = Units.map (k ≫ g).appTop.hom.toMonoidHom u := by
    rw [← map_pow, ha, umap_comp]
  have hb' : b ^ q = Units.map (k ≫ g).appTop.hom.toMonoidHom v := by rw [hb, umap_comp]
  rw [h₁ W' (k ≫ g) _ b ha' hb', h₂ W' (k ≫ g) _ b ha' hb']

theorem KP_exists (hk : IsKum q (kumT q)) (hp : EtalePrimitiveRootsExistLocally) (hs : EtaleSheafSectionsSeparatedAndGlue) [NeZero q]
    {V : Scheme.{0}} (hq : IsUnit (q : Γ(V, ⊤))) (u v : (Γ(V, ⊤))ˣ) : ∃ Z, KP q u v Z := by
  classical
  let S : Sieve V :=
    { arrows := fun W g => (∃ a : (Γ(W, ⊤))ˣ, a ^ q = Units.map g.appTop.hom.toMonoidHom u) ∧
        ∃ b : (Γ(W, ⊤))ˣ, b ^ q = Units.map g.appTop.hom.toMonoidHom v
      downward_closed := by
        rintro W W' g ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ k
        exact ⟨⟨Units.map k.appTop.hom.toMonoidHom a, by rw [← map_pow, ha, umap_comp]⟩,
          ⟨Units.map k.appTop.hom.toMonoidHom b, by rw [← map_pow, hb, umap_comp]⟩⟩ }
  have hS : S ∈ Scheme.etaleTopology V := by
    obtain ⟨S₁, h₁, P₁⟩ := (hp q V).2.2.2 hq u
    obtain ⟨S₂, h₂, P₂⟩ := (hp q V).2.2.2 hq v
    refine Scheme.etaleTopology.superset_covering ?_ (Scheme.etaleTopology.intersection_covering h₁ h₂)
    intro W g hg
    exact ⟨P₁ W g hg.1, P₂ W g hg.2⟩
  let sfun : ∀ (W : Scheme.{0}) (g : W ⟶ V), S.arrows g → Sec ((res _ (tw q 1)).X 0) W :=
    fun W g hg => D q W (Classical.choose (And.left hg)) (Classical.choose (And.right hg))
  obtain ⟨Z, hZ⟩ := (hs _ _ V).2 S hS sfun (by
    intro W W' g k hg
    rw [D_res q hk k (unit_q q g hq)]
    refine D_change2 q hk hp hs (unit_q q (k ≫ g) hq) _ _ _ _ ?_ ?_
    · rw [← map_pow, hg.1.choose_spec, ← umap_comp, (S.downward_closed hg k).1.choose_spec]
    · rw [← map_pow, hg.2.choose_spec, ← umap_comp, (S.downward_closed hg k).2.choose_spec])
  refine ⟨Z, fun W g a b ha hb => ?_⟩
  have hg : S.arrows g := ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rw [hZ W g hg]
  exact D_change2 q hk hp hs (unit_q q g hq) _ _ _ _ (by rw [hg.1.choose_spec, ha]) (by rw [hg.2.choose_spec, hb])

theorem res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (s t : Sec F U) :
    Sec.res g (s + t) = Sec.res g s + Sec.res g t := map_add _ _ _

noncomputable def yv {X : Scheme.{0}} (Y : ∀ U : Scheme.{0}, (U ⟶ X) → Sec ((res (ZMod q) (tw q 1)).X 0) U) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 0 = s → ∀ U : Scheme.{0}, Sx (sch.obj X) p U → Sec ((res (ZMod q) (tw q 1)).X s) U
  | 0, s, h, U, x => by
      obtain rfl : s = 0 := by simpa using h.symm
      exact Y U x
  | _ + 1, _, _, _, _ => 0

end LateralTheory.EtaleFoundations.KMC

namespace LateralTheory.EtaleFoundations
open KMC

theorem kum_mul_coc_of (hkT : EtaleKummerTriangleExists) (hp : EtalePrimitiveRootsExistLocally) (hs : EtaleSheafSectionsSeparatedAndGlue)
    (hmk : EtaleCochainExistsOfNaturalEvaluation) (hd : EtaleCochainEvaluationCoboundaryFormula) (hb : EtaleCochainEvaluationLinear) : kum_mul_coc := by
  intro q _ X u v hq γu γv ku kv
  have hk := hkT q
  have hY : ∀ (U : Scheme.{0}) (x : U ⟶ X), ∃ Z, KP q (Units.map x.appTop.hom.toMonoidHom u)
      (Units.map x.appTop.hom.toMonoidHom v) Z :=
    fun U x => KP_exists q hk hp hs (unit_q q x hq) _ _
  choose Y hYP using hY
  have hYnat : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : U ⟶ X), Sec.res g (Y U x) = Y V (g ≫ x) := by
    intro V U g x
    refine KP_uniq q hp hs (unit_q q (g ≫ x) hq) ?_ (hYP V (g ≫ x))
    have := KP_res q g (hYP U x)
    rwa [← umap_comp, ← umap_comp] at this
  obtain ⟨y, hy⟩ := hmk (ZMod q) (E := sch.obj X) (I := res _ (tw q 1)) (n := 0) (yv q Y) (by
    intro p s h V U g x
    cases p with
    | zero =>
      obtain rfl : s = 0 := by simpa using h.symm
      exact hYnat V U g x
    | succ p =>
      show Sec.res g 0 = 0
      exact map_zero _)
  let β : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1 :=
    Cocycle.mk (δ 0 1 y) 2 (by norm_num) (δ_δ 0 1 2 y)
  have e : (γu + γv + β).1 = γu.1 + γv.1 + δ 0 1 y := rfl
  have hadd1 : ∀ (α β' : Cochain ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1) (U : Scheme.{0}) (x : U ⟶ X),
      ev (α + β') 1 0 (by simp) U x = ev α 1 0 (by simp) U x + ev β' 1 0 (by simp) U x :=
    fun α β' U x => ((hb (ZMod q)).1 α β' 1 0 _ U x).1
  have hadd0 : ∀ (α β' : Cochain ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1) (U : Scheme.{0}) (x : U ⟶ X),
      ev (α + β') 0 1 (by simp) U x = ev α 0 1 (by simp) U x + ev β' 0 1 (by simp) U x :=
    fun α β' U x => ((hb (ZMod q)).1 α β' 0 1 _ U x).1
  have hδ0 : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev (δ 0 1 y) 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (Y U x) :=
    fun U x => ((hd (ZMod q) (n := 0) (m := 1) rfl y U).1 x).trans (congrArg _ (hy 0 0 _ U x))
  refine ⟨γu + γv + β, ⟨?_, ?_⟩, ?_⟩
  · intro U x
    rw [e]
    rw [hadd1, hadd1]
    rw [ku.1 U x, kv.1 U x, zero_add, zero_add]
    refine ((hd (ZMod q) (n := 0) (m := 1) rfl y U).2 0 (-1) 0 (by simp) (by simp) x).trans ?_
    have hy1 : ev y (0 + 1) (-1) (by simp) U x = 0 := hy 1 (-1) _ U x
    have hface : ∀ i, ev y 0 0 (by simp) U (Sx.face (E := sch.obj X) (p := 0) x i) = Y U x := fun i => hy 0 0 _ U _
    rw [hy1]
    simp only [hface]
    simp [Fin.sum_univ_two, Sec.map]
  · intro U x w hw
    rw [e]
    rw [hadd0, hadd0, hδ0]
    apply (hs _ _ U).1
    refine loc_mono ((hp q U).2.2.2 (unit_q q x hq) (Units.map x.appTop.hom.toMonoidHom u)) (fun W k ha => ?_)
    obtain ⟨a, ha⟩ := ha
    set K := Units.map k.appTop.hom.toMonoidHom w with hK
    have hbq : (K * a⁻¹) ^ q = Units.map k.appTop.hom.toMonoidHom (Units.map x.appTop.hom.toMonoidHom v) := by
      rw [mul_pow, inv_pow, hK, ← map_pow, hw, ha, map_mul, map_mul, mul_comm (Units.map _ (Units.map _ u)),
        mul_inv_cancel_right]
    have hab : a * (K * a⁻¹) = K := by rw [mul_comm K, mul_inv_cancel_left]
    have eu : Sec.res k (ev γu.1 0 1 (by simp) U x) = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q W a) :=
      ((hb (ZMod q)).2.1 γu.1 0 1 (by simp) W U k x).trans (ku.2 W (k ≫ x) a (by rw [ha, umap_comp]))
    have ev' : Sec.res k (ev γv.1 0 1 (by simp) U x) = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q W (K * a⁻¹)) :=
      ((hb (ZMod q)).2.1 γv.1 0 1 (by simp) W U k x).trans (kv.2 W (k ≫ x) _ (by rw [hbq, umap_comp]))
    rw [res_add, res_add, eu, ev', res_map, res_map, hYP U x W k a (K * a⁻¹) ha hbq, hk.1 W U k w (unit_q q x hq)]
    rw [← hK]
    unfold D
    rw [hab]
    simp only [Sec.map, map_sub]
    abel
  · rw [CohomologyClass.mk_add, CohomologyClass.mk_add,
      (CohomologyClass.mk_eq_zero_iff β).2 ((mem_coboundaries_iff β 0 (by norm_num)).2 ⟨y, rfl⟩), add_zero]

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.KumPowCocPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

abbrev LkumTex : Prop := ∀ (q : ℕ) [NeZero q], IsKum q (kumT q)

abbrev LevMk : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

abbrev LevDelta : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m)
  (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}),
  (∀ (x : Sx E 0 U), ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x)) ∧
  ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U),
    ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
      m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i)

lemma units_map_appTop_comp {V U X : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (u : (Γ(X, ⊤))ˣ) :
    Units.map g.appTop.hom.toMonoidHom (Units.map x.appTop.hom.toMonoidHom u) =
      Units.map (g ≫ x).appTop.hom.toMonoidHom u := by
  ext; simp; rfl

lemma isUnit_q_pull {U X : Scheme.{0}} (q : ℕ) (x : U ⟶ X) (hq : IsUnit (q : Γ(X, ⊤))) :
    IsUnit (q : Γ(U, ⊤)) := by
  simpa using hq.map x.appTop.hom

theorem kum_pow_coc_of (hk : LkumTex) (hmk : LevMk) (hd : LevDelta) (he : kum_exists) : kum_pow_coc := by
  intro q _ X u hq
  let I := res _ (tw q 1)
  let a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 0 = s → ∀ U : Scheme.{0}, Sx (sch.obj X) p U → Sec (I.X s) U :=
    fun p s _ U x => if hs : s = 0 then (by subst hs; exact kumT q U (Units.map (x : U ⟶ X).appTop.hom.toMonoidHom u))
      else 0
  have ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx (sch.obj X) p U),
      Sec.res g (a p s h U x) = a p s h V (x.res g) := by
    intro p s h V U g x
    by_cases hs : s = 0
    · subst hs
      simp only [a, dif_pos]
      rw [(hk q).1 V U g _ (isUnit_q_pull q x hq)]
      exact congrArg (kumT q V) (units_map_appTop_comp g x u)
    · simp only [a, dif_neg hs, map_zero]
  obtain ⟨α, hα⟩ := hmk (ZMod q) a ha
  refine ⟨Cocycle.mk (δ 0 1 α) 2 (by norm_num) (δ_δ 0 1 2 α), ⟨?_, ?_⟩, ?_⟩
  · have key : ∀ (U : Scheme.{0}) (x : Sx (sch.obj X) (0 + 1) U), ev (δ 0 1 α) (0 + 1) 0 (by simp) U x = 0 := by
      intro U x
      rw [(hd (ZMod q) (n := 0) (m := 1) (by norm_num) α U).2 0 (-1) 0 (by simp) (by simp) x, hα]
      have z : a (0 + 1) (-1) (by simp) U x = 0 := dif_neg (by norm_num)
      have f0 : x.face 0 = x.face 1 := rfl
      rw [z, Fin.sum_univ_two, f0]
      simp [Sec.map]
    exact fun U x => key U x
  · intro U x v hv
    obtain ⟨γ0, _, hγ0⟩ := he q X (u ^ q) hq
    have e1 := hγ0 U x v hv
    have e2 := hγ0 U x (Units.map x.appTop.hom.toMonoidHom u) (by rw [map_pow])
    have h1 := (hd (ZMod q) (n := 0) (m := 1) (by norm_num) α U).1 x
    refine h1.trans ?_
    erw [hα]
    simp only [a, dif_pos]
    exact e2.symm.trans e1
  · rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨0, by norm_num, α, rfl⟩

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.KumUniqPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def uniq_prim_loc : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)

def sections_unique_of_local_agreement : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

def uniq_ev_basic : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

theorem sec_neg_eq (q : ℕ) [NeZero q] (s : ℤ) (hs : s < 0) (U : Scheme.{0})
    (a b : Sec ((res _ (tw q 1)).X s) U) : a = b := by
  have h0 : IsZero ((res _ (tw q 1)).X s) := by
    unfold res
    exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)
  have h1 : IsZero (((res _ (tw q 1)).X s).obj.obj (op U)) :=
    ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)).map_isZero h0)
  have : Subsingleton (((res _ (tw q 1)).X s).obj.obj (op U)) :=
    (ModuleCat.isZero_iff_subsingleton).mp h1
  exact Subsingleton.elim a b

theorem root_res (q : ℕ) (X U V : Scheme.{0}) (u : (Γ(X, ⊤))ˣ) (x : U ⟶ X) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ)
    (hv : v ^ q = Units.map g.appTop.hom.toMonoidHom (Units.map x.appTop.hom.toMonoidHom u)) :
    v ^ q = Units.map (Sx.res (E := sch.obj X) (p := 0) g x : V ⟶ X).appTop.hom.toMonoidHom u := by
  have e : (Sx.res (E := sch.obj X) (p := 0) g x : V ⟶ X) = g ≫ x := rfl
  rw [hv, e]; ext; simp
  rfl

theorem kum_uniq_of (hl : uniq_prim_loc) (hg : sections_unique_of_local_agreement) (hb : uniq_ev_basic) : kum_uniq := by
  intro q _ X u hq γ γ' h h'
  have key : γ = γ' := by
    apply Subtype.ext
    apply (hb (ZMod q)).2.2.1
    intro p s hs U x
    rcases p with _ | _ | p
    · have hs' : s = 1 := by omega
      subst hs'
      have hqU : IsUnit ((q : ℕ) : Γ(U, ⊤)) := by
        have := hq.map x.appTop.hom
        simpa using this
      obtain ⟨S, hS, hP⟩ := (hl q U).2.2.2 hqU (Units.map x.appTop.hom.toMonoidHom u)
      apply (hg (ZMod q) _ U).1
      refine ⟨S, hS, fun V g hgS => ?_⟩
      obtain ⟨v, hv⟩ := hP V g hgS
      rw [(hb (ZMod q)).2.1, (hb (ZMod q)).2.1]
      have hv' := root_res q X U V u x g v hv
      rw [h.2 V _ v hv', h'.2 V _ v hv']
    · have hs' : s = 0 := by omega
      subst hs'
      rw [h.1 U x, h'.1 U x]
    · exact sec_neg_eq q s (by omega) U _ _
  rw [key]

end LateralTheory.EtaleFoundations
end

