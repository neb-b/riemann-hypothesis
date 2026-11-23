module

public import Development.WeilBound.ThetaLifts.CartanFactorisation.ActsComp
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle0005
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.CartanFactorisation.CommuteConj
section
noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem re_mul {m : ℕ} {Y : Spc F E m} {R : Type} [Zero R] {ev : AF F → R} {g k : UA σ Y.J} (hg : g ∈ UAt σ Y ev)
    (hk : k ∈ UAt σ Y ev) : g * k ∈ UAt σ Y ev := fun u hu => by
  have e : mat (g * k) - 1 = mat g * (mat k - 1) + (mat g - 1) := by
    rw [show mat (g * k) = mat g * mat k from rfl, Matrix.mul_sub, Matrix.mul_one]; abel
  rw [e, smul_add, hg u hu, ← Matrix.mul_smul, hk u hu, Matrix.mul_zero, add_zero]

theorem re_inv {m : ℕ} {Y : Spc F E m} {R : Type} [Zero R] {ev : AF F → R} {g : UA σ Y.J} (hg : g ∈ UAt σ Y ev) :
    g⁻¹ ∈ UAt σ Y ev := fun u hu => by
  have h1 : mat g⁻¹ * mat g = 1 := by rw [← show mat (g⁻¹ * g) = mat g⁻¹ * mat g from rfl, inv_mul_cancel]; rfl
  have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by rw [Matrix.mul_sub, h1, Matrix.mul_one]; abel
  rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]

theorem conj_line {m : ℕ} {Y : Spc F E m} {g : UA σ Y.J} (hg : g ∈ UAt σ Y (evI F)) {γ} (hγ : γ ∈ Lines σ Y) :
    (MulAut.conj g).toMonoidHom.comp γ ∈ Lines σ Y :=
  ⟨show Continuous fun t => g * γ t * g⁻¹ from (continuous_const.mul hγ.1).mul continuous_const,
    fun t => re_mul (re_mul hg (hγ.2 t)) (re_inv hg)⟩

theorem commute_conj {G M : Type} [Group G] [Monoid M] (φ : G →* M) {g k : G} {t t₂ : M} (h : φ g * t₂ = t * φ g)
    (hk : Commute (φ k) t₂) : Commute (φ (g * k * g⁻¹)) t := by
  have h' : φ g⁻¹ * t = t₂ * φ g⁻¹ := by
    calc φ g⁻¹ * t = φ g⁻¹ * (t * φ g) * φ g⁻¹ := by rw [mul_assoc, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
      _ = t₂ * φ g⁻¹ := by rw [← h, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  show _ * t = t * _
  rw [map_mul, map_mul, mul_assoc, h', ← mul_assoc, mul_assoc (φ g), hk.eq, ← mul_assoc, h]
  simp only [mul_assoc]

theorem cj1 {G H : Type} [Group G] [Group H] (g x : G) (h : H) : (g * x * g⁻¹, (1 : H)) * (g, h) = (g, h) * (x, 1) := by simp

theorem cj2 {G H : Type} [Group G] [Group H] (g : G) (h x : H) : ((1 : G), h * x * h⁻¹) * (g, h) = (g, h) * (1, x) := by simp

theorem cj3 {G H : Type} [Group G] [Group H] (g : G) (h x : H) : ((1 : G), x) * (g, h) = (g, h) * (1, h⁻¹ * x * h⁻¹⁻¹) := by
  simp [mul_assoc]

theorem inv_rel {G M : Type} [Group G] [Monoid M] (φ : G →* M) {g : G} {t t₂ : M} (h : φ g * t₂ = t * φ g) :
    φ g⁻¹ * t = t₂ * φ g⁻¹ := by
  calc φ g⁻¹ * t = φ g⁻¹ * (t * φ g) * φ g⁻¹ := by rw [mul_assoc, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    _ = t₂ * φ g⁻¹ := by rw [← h, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

def matC {m : ℕ} (J : Matrix (Fin m) (Fin m) E) {w : InfinitePlace F} (τ : EmbOver E w) : UA σ J →* Matrix (Fin m) (Fin m) ℂ :=
  (piInf τ).mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp (Subgroup.subtype _))

def Moves (B : Base F E) {m : ℕ} (Y Y₂ : Spc F E m) (g : UA σ Y.J) : Prop :=
  g ∈ UAt σ Y (evI F) ∧ ∀ w, (mat g).map (piInf (B.emb w)) * Y₂.θ w = Y.θ w * (mat g).map (piInf (B.emb w))

theorem Moves.up {B : Base F E} {m : ℕ} {Y Y₂ : Spc F E m} {g : UA σ Y.J} (h : Moves B Y Y₂ g) {k : UA σ Y.J}
    (hk : k ∈ KInf σ (reS Y Y₂) B.emb) : g * k * g⁻¹ ∈ KInf σ Y B.emb :=
  ⟨re_mul (re_mul h.1 hk.1) (re_inv h.1), fun w => commute_conj (matC Y.J (B.emb w)) (h.2 w) (hk.2 w)⟩

theorem Moves.down {B : Base F E} {m : ℕ} {Y Y₂ : Spc F E m} {g : UA σ Y.J} (h : Moves B Y Y₂ g) {k : UA σ Y.J}
    (hk : k ∈ KInf σ Y B.emb) : g⁻¹ * k * g⁻¹⁻¹ ∈ KInf σ (reS Y Y₂) B.emb :=
  ⟨re_mul (Y := Y) (re_mul (re_inv h.1) hk.1) (re_inv (re_inv h.1)),
    fun w => commute_conj (matC Y.J (B.emb w)) (inv_rel (matC Y.J (B.emb w)) (h.2 w)) (hk.2 w)⟩

section Pair

variable {n d : ℕ} {X X₂ : Spc F E n} {W W₂ : Spc F E d} {B : Base F E} {M : Model σ X W} {M₂ : Model σ (reS X X₂) (reS W W₂)}
  {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

theorem transK (hO : ArchOp) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s') {g h T} (hT : IsArchOp om (g, h) T)
    {x₁ x₂ y₁ y₂} (h1 : x₁ ∈ UAt σ X (evI F)) (h2 : x₂ ∈ UAt σ W (evI F)) (e : (x₁, x₂) * (g, h) = (g, h) * (y₁, y₂))
    {f f₁ : SInf F (Fin n × Fin d)} (ha : Acts (evI F) (om (y₁, y₂)) f f₁) : Acts (evI F) (om (x₁, x₂)) (T f) (T f₁) := by
  obtain ⟨T₁, hT₁, -⟩ := hO F E σ B n d X W M χX χW om r s r' s' hp x₁ h1 x₂ h2
  have a := acts_comp hp (hT.2 f) (hT₁.2 (T f))
  rw [e] at a
  rw [(hQ F _ f _ _).1 _ (acts_comp hp ha (hT.2 f₁)) a]
  exact hT₁.2 _

theorem transL (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s')
    (hp₂ : IsPair B M₂ χX χW om r s r' s') {g h T} (hT : IsArchOp om (g, h) T)
    (hP : (M₂.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) = M.Pol B.ψ B.emb) {γ δ γ₂ δ₂} (hγ : γ ∈ Lines σ X) (hδ : δ ∈ Lines σ W)
    (hγ₂ : γ₂ ∈ Lines σ X) (hδ₂ : δ₂ ∈ Lines σ W) (e : ∀ t, (γ t, δ t) * (g, h) = (g, h) * (γ₂ t, δ₂ t))
    {f f₁ : SInf F (Fin n × Fin d)} (hf : f ∈ M₂.Pol B.ψ B.emb)
    (ha : ActsD (evI F) (fun t => om (γ₂ (Multiplicative.ofAdd t), δ₂ (Multiplicative.ofAdd t))) f f₁) :
    ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), δ (Multiplicative.ofAdd t))) (T f) (T f₁) := by
  have hO' := hO
  choose op hop _ using hO F E σ B n d X W M χX χW om r s r' s' hp
  obtain ⟨z, -, z2, z3⟩ := hL F E σ B n d _ _ M₂ χX χW om r s r' s' hp₂ γ₂ hγ₂ δ₂ hδ₂
    (fun t => op _ (hγ₂.2 _) _ (hδ₂.2 _)) (fun t => hop _ _ _ _) f hf
  obtain ⟨y, -, y2, y3⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp γ hγ δ hδ
    (fun t => op _ (hγ.2 _) _ (hδ.2 _)) (fun t => hop _ _ _ _) (T f) (hP ▸ ⟨f, hf, rfl⟩)
  rw [(hQ F _ f f₁ z).2 _ ha z2, sinf_ext (f := T z) (g := y) fun L => ?_]
  · exact y2
  refine HasDerivAt.unique (z3 (L.comp T)) ?_
  refine (y3 L).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  exact congrArg L ((hQ F _ _ _ _).1 _ (transK hO' hQ hp hT (hγ.2 _) (hδ.2 _) (e _) ((hop _ _ _ _).2 f)) ((hop _ _ _ _).2 _))

theorem quot_trans (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s')
    (hp₂ : IsPair B M₂ χX χW om r s r' s') {g h T} (hg : Moves B X X₂ g) (hT : IsArchOp om (g, h) T)
    (hP : (M₂.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) = M.Pol B.ψ B.emb) {P : Type} [AddCommGroup P] [Module ℂ P]
    {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P} (q : RealQuot B M om p) : RealQuot B M₂ om (p ∘ₗ (T : _ →ₗ[ℂ] _)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Submodule.map_comp, hP, q.onto]
  · exact fun γ hγ f hf f₁ ha => q.lie _ (conj_line hg.1 hγ) (T f) (hP ▸ ⟨f, hf, rfl⟩) (T f₁)
      (transL hO hL hQ hp hp₂ hT hP (conj_line hg.1 hγ) one_line hγ one_line (fun t => cj1 g (γ t) h) hf ha)
  · exact fun k hk f hf f₁ ha => q.cpt _ (hg.up hk) (T f) (hP ▸ ⟨f, hf, rfl⟩) (T f₁)
      (transK hO hQ hp hT (hg.up hk).1 (one_at _) (cj1 g k h) ha)

theorem exists_linop (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s') (i) :
    ∃ A : M.Pol B.ψ B.emb →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ x, A x ∈ M.Pol B.ψ B.emb ∧ ∀ y, RInf B om i x y ↔ y = A x := by
  choose op hop hopP using hO F E σ B n d X W M χX χW om r s r' s' hp
  rcases i with δ | k
  · choose D h3 h4 h5 using hL F E σ B n d X W M χX χW om r s r' s' hp 1 one_line δ δ.2
      (fun t => op 1 (one_at _) _ (δ.2.2 _)) fun t => hop 1 _ _ _
    refine ⟨{ toFun := fun x => D x x.2
              map_add' := fun x y => sinf_ext fun L => ?_
              map_smul' := fun c x => sinf_ext fun L => ?_ }, fun x => ⟨h3 x x.2, fun y =>
      ⟨fun h => ((hQ F _ x.1 (D x x.2) y).2 _ (h4 x x.2) h).symm, fun h => by rw [h]; exact h4 x x.2⟩⟩⟩
    · refine (h5 _ (x + y).2 L).unique ?_
      simp only [Submodule.coe_add, map_add (f := _)]
      exact (h5 x x.2 L).add (h5 y y.2 L)
    · refine (h5 _ (c • x).2 L).unique ?_
      simp only [Submodule.coe_smul, map_smul, RingHom.id_apply]
      exact (h5 x x.2 L).const_smul c
  · exact ⟨(op 1 (one_at _) k k.2.1 : _ →ₗ[ℂ] _) ∘ₗ Submodule.subtype _, fun x => ⟨hopP 1 _ k _ (one_kinf _) k.2 x x.2, fun y =>
      ⟨fun h => ((hQ F _ x.1 _ y).1 _ ((hop 1 (one_at _) k k.2.1).2 x) h).symm,
        fun h => by rw [h]; exact (hop 1 (one_at _) k k.2.1).2 x⟩⟩⟩

end Pair

end PositivityTheory.ThKF

end
end

-- bundled from Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsEnlarge
section
noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKG
open scoped Classical

theorem exists_enlarge {α : Type} {Q : α → Type} [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] (z : ∀ v, Q v)
    {T T' : Finset α} (h : T ⊆ T') : ∃ L : PiTensorProduct ℂ (fun v : T => Q v) →ₗ[ℂ] PiTensorProduct ℂ (fun v : T' => Q v),
      ∀ y : ∀ v, Q v, (∀ v ∉ T, y v = z v) →
        L (PiTensorProduct.tprod ℂ fun v : T => y v) = PiTensorProduct.tprod ℂ fun v : T' => y v := by
  let e : (∀ v : T, Q v) → ∀ v : T', Q v := fun ψ v => if hv : v.1 ∈ T then ψ ⟨v, hv⟩ else z v
  have he : ∀ [DecidableEq T] (ψ : ∀ v : T, Q v) (i : T) (x : Q i),
      e (Function.update ψ i x) = Function.update (e ψ) ⟨i.1, h i.2⟩ x := by
    intro _ ψ i x
    funext v
    by_cases hv : v = ⟨i.1, h i.2⟩
    · subst hv; simp only [e, dif_pos i.2, Function.update_self]
    · rw [Function.update_of_ne hv]
      simp only [e]
      split_ifs with hT
      · exact Function.update_of_ne (f := ψ) (a := ⟨v.1, hT⟩) (a' := i) (fun k => hv (Subtype.ext (congrArg Subtype.val k :))) _
      · rfl
  refine ⟨PiTensorProduct.lift
    { toFun := fun ψ => PiTensorProduct.tprod ℂ (e ψ)
      map_update_add' := fun ψ i x y => by rw [he, he, he, MultilinearMap.map_update_add]
      map_update_smul' := fun ψ i c x => by rw [he, he, MultilinearMap.map_update_smul] }, fun y hy => ?_⟩
  rw [PiTensorProduct.lift.tprod]
  change PiTensorProduct.tprod ℂ (e fun v => y v) = _
  congr 1
  funext v
  simp only [e]
  split_ifs with hv
  exacts [rfl, (hy v hv).symm]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem kill_aug (hI : ILeft) {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}
    (hp : IsPair B M χX χW om r s r' s') (J : Fn F n d →ₗ[ℂ] (UA σ W.J → ℂ)) (hJ : ∀ Φ ∈ schA F _, J Φ = M.I om Φ)
    (v : Pl F) (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (h1 : ∀ v, φ v ∈ SB _) (h2 : Std φ)
    (z : (Fin n × Fin d → Fv F v) → ℂ) (hz : z ∈ augAt om v) : J (pure f (Function.update φ v z)) = 0 := by
  obtain ⟨ρ, hρ, hρ'⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ h2
  let t : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] Fn F n d :=
    { toFun := fun z => tens (evFin F v) z ρ
      map_add' := fun x y => funext fun _ => add_mul _ _ _
      map_smul' := fun a x => funext fun _ => mul_assoc _ _ _ }
  have mem : ∀ y ∈ SB _, t y ∈ schA F _ := fun y hy => by
    change tens (evFin F v) y ρ ∈ _
    rw [hρ']
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun u => ?_) (GlobalTheory.PureFactor.update_eventually φ v y h2)
    by_cases hu : u = v
    · subst hu; rw [Function.update_self]; exact hy
    · rw [Function.update_of_ne hu]; exact h1 u
  rw [← hρ']
  change (J ∘ₗ t) z = 0
  refine (Submodule.span_le.2 ?_ : augAt om v ≤ LinearMap.ker (J ∘ₗ t)) hz
  rintro _ ⟨g, -, y, hy, y₁, hy₁, ha, rfl⟩
  have e : om (g, 1) (t y) = t y₁ := ha ρ ⟨hρ, mem y hy⟩
  change J (t (y₁ - y)) = 0
  rw [map_sub, map_sub, hJ _ (mem y₁ hy₁), hJ _ (mem y hy), ← e, hI F E σ B n d X W M χX χW om r s r' s' hp _ (mem y hy), sub_self]

theorem anAll_of (hW : WeilConv) (hC : KCoinv) (hI : ILeft) : AnAll := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hm hq c hc Φ Φ' ⟨T, hT, m, m', f, φ, f', φ', h1, h2, e1, e2, e⟩ h
  have g := hm.triple.geo.hM
  have g' := hm.triple.geo.hM'
  have hp : IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q)
      (a + a' - (G.p + G.q)) (G.p + G.q) := by
    have hd : IsHecke F E (X.α / X.β) :=
      ⟨hm.triple.chars.heckeα.1.div' hm.triple.chars.heckeβ.1, fun x => by
        rw [MonoidHom.div_apply, hm.triple.chars.heckeα.2, hm.triple.chars.heckeβ.2, div_one]⟩
    have hr : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (X.α / X.β) (a + a') := by
      intro x
      rw [MonoidHom.div_apply, Circle.coe_div, hm.triple.chars.resα, hm.triple.chars.resβ, add_comm a a']
      split_ifs
      · simp
      · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]
    exact ⟨hm.triple.base, hm.triple.geo.hV', hm.triple.geo.hW, g',
      hm.triple.chars.heckeα, hd, hm.triple.chars.resα, hr, hm.triple.weil'⟩
  obtain ⟨J, hJ⟩ := exists_Ilin hm.triple.weil' (schA F _) le_rfl fun Φ hΦ =>
    ((hW F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hp (Or.inr (by rw [hq]; simp))).1 Φ hΦ).1
  obtain ⟨-, c2, c3, -⟩ := (hC F E σ B a a' G X om om' R Rf hm).1 B.v₁ hm.triple.chars.good
  choose y hy hy' using fun j => c3 B.τ₁ (Rf.p' B.v₁ (φ' j B.v₁))
  let φ₀ : Fin m' → ∀ v : Pl F, _ := fun j => Function.update (φ' j) B.v₁ (y j)
  have sb : ∀ j v, φ₀ j v ∈ SB _ := fun j v => by
    by_cases hv : v = B.v₁
    · subst hv; simp only [φ₀, Function.update_self]; exact (hy j).1
    · simp only [φ₀, Function.update_of_ne hv]; exact (h2 j).2.1 v
  have off : ∀ j, ∀ v ∉ insert B.v₁ T, φ₀ j v = G.M'.vac v := fun j v hv => by
    rw [Finset.mem_insert, not_or] at hv
    simp only [φ₀, Function.update_of_ne hv.1]; exact (h2 j).2.2 v hv.2
  have pe : ∀ j v, Rf.p' v (φ₀ j v) = Rf.p' v (φ' j v) := fun j v => by
    by_cases hv : v = B.v₁
    · subst hv; simp only [φ₀, Function.update_self]; exact hy' j
    · simp only [φ₀, Function.update_of_ne hv]
  have so : ∑ j, pure (f' j) (φ₀ j) ∈ G.M'.So B.ψ B.τ₁ := sum_mem fun j _ =>
    pure_mem_So g' _ _ _ (fun v _ => sb j v) (ev_of_off (off j))
      (by simp only [φ₀, Function.update_self]; exact Submodule.subset_span (hy j))
  obtain ⟨L, hL⟩ := exists_enlarge (fun v => Rf.p v (G.M.vac v)) (Finset.subset_insert B.v₁ T)
  have pm : PolMatch B G X R Rf Φ (∑ j, pure (f' j) (φ₀ j)) := by
    refine ⟨insert B.v₁ T, hT.trans (Finset.subset_insert _ _), m, m', f, φ, f', φ₀,
      fun i => ⟨(h1 i).1, (h1 i).2.1, fun v hv => (h1 i).2.2 v fun k => hv (Finset.mem_insert_of_mem k)⟩,
      fun j => ⟨(h2 j).1, sb j, off j⟩, e1, rfl, ?_⟩
    have := congrArg (TensorProduct.map LinearMap.id L) e
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply] at this
    simp only [pe]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (this.trans (Finset.sum_congr rfl fun j _ => ?_))
    · rw [hL (fun v => Rf.p v (φ i v)) fun v hv => by rw [(h1 i).2.2 v hv]]
    · rw [hL (fun v => Rf.p' v (φ' j v)) fun v hv => by
        rw [(h2 j).2.2 v hv, (hm.fin.sph v fun k => hv (hT k)).1]]
  rw [hc Φ _ so pm h]
  congr 1
  have st : ∀ j, Std (φ' j) := fun j => (good_std g').congr (ev_of_off (h2 j).2.2)
  have m1 : Φ' ∈ schA F _ := e2 ▸ sum_mem fun j _ => GlobalTheory.TensUniq.pure_mem_schA _ _ (h2 j).2.1 (st j)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hJ _ (so_le g' _ so), ← hJ _ m1, e2, map_sum, map_sum]
  refine congrFun (Finset.sum_congr rfl fun j _ => ?_) h
  have k := kill_aug hI hp J hJ B.v₁ (f' j) (φ' j) (h2 j).2.1 (st j) (y j - φ' j B.v₁)
    ((c2 _ (sub_mem (hy j).1 ((h2 j).2.1 _))).1 (by rw [map_sub, hy', sub_self]))
  have a2 := (pureAct F _ B.v₁ id (f' j) (φ' j) (h2 j).2.1 (st j)).2.1 (φ' j B.v₁) (y j - φ' j B.v₁) 1
  rw [one_smul, one_smul, add_sub_cancel, Function.update_eq_self] at a2
  have k' : J (pure (f' j) (φ₀ j)) = J (pure (f' j) (φ' j)) := by
    have := congrArg J a2
    rw [map_add (f := _)] at this
    exact this.trans (by rw [show J _ = 0 from k, add_zero])
  exact k'

end PositivityTheory.ThKF

end
end

