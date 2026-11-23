module

public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle0004
public import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.CartanFactorisation.RinfZero
section
noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem absMax {Q Q' P ι : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Q'] [Module ℂ Q'] [AddCommGroup P] [Module ℂ P]
    {p : Q →ₗ[ℂ] P} {p' : Q' →ₗ[ℂ] P} {S : Submodule ℂ Q} {S' : Submodule ℂ Q'} {R : ι → Q → Q → Prop} {R' : ι → Q' → Q' → Prop}
    (on : S.map p = ⊤) (on' : S'.map p' = ⊤) (ex : ∀ i, ∀ x ∈ S, ∃ y, R i x y) (ex' : ∀ i, ∀ x ∈ S', ∃ y, R' i x y)
    (z : ∀ i, R i 0 0) (z' : ∀ i, R' i 0 0)
    (eqv : ∀ i, ∀ x ∈ S, ∀ x' ∈ S', ∀ y y', R i x y → R' i x' y' → p x = p' x' → p y = p' y')
    (irr : ∀ N : Submodule ℂ P, (∀ i, ∀ x ∈ S, ∀ y, R i x y → p x ∈ N → p y ∈ N) → N = ⊥ ∨ N = ⊤) :
    ((∀ i, ∀ x ∈ S, ∀ y, R i x y → p x = 0 → p y = 0) ∧
      ∀ N ≤ S, (∀ i, ∀ x ∈ N, ∀ y, R i x y → y ∈ N) → N.map p = ⊥ ∨ N.map p = ⊤) ∧
    (∀ i, ∀ x ∈ S', ∀ y, R' i x y → p' x = 0 → p' y = 0) ∧
      ∀ N ≤ S', (∀ i, ∀ x ∈ N, ∀ y, R' i x y → y ∈ N) → N.map p' = ⊥ ∨ N.map p' = ⊤ := by
  refine ⟨⟨fun i x hx y h h0 => by simpa using eqv i x hx 0 S'.zero_mem y 0 h (z' i) (by simpa using h0), fun N hN hs => irr _ ?_⟩,
    fun i x hx y h h0 => by simpa using (eqv i 0 S.zero_mem x hx 0 y (z i) h (by simpa using h0.symm)).symm,
    fun N hN hs => irr _ ?_⟩
  · rintro i x hx y h ⟨w, hw, e⟩
    obtain ⟨x', hx', e'⟩ : p x ∈ S'.map p' := on' ▸ Submodule.mem_top
    obtain ⟨y', hy'⟩ := ex' i x' hx'
    obtain ⟨w₁, hw₁⟩ := ex i w (hN hw)
    exact ⟨w₁, hs i w hw w₁ hw₁,
      (eqv i w (hN hw) x' hx' w₁ y' hw₁ hy' (e.trans e'.symm)).trans (eqv i x hx x' hx' y y' h hy' e'.symm).symm⟩
  · rintro i x hx y h ⟨w, hw, e⟩
    obtain ⟨w₁, hw₁⟩ := ex' i w (hN hw)
    exact ⟨w₁, hs i w hw w₁ hw₁, (eqv i x hx w (hN hw) y w₁ h hw₁ e.symm).symm⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Pair

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
  {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

theorem acts_zero {R κ : Type} [Zero R] [Fintype κ] (ev : AF F → R) (T : Module.End ℂ ((κ → AF F) → ℂ)) : Acts ev T 0 0 :=
  fun r _ => by
    have : tens ev 0 r = 0 := funext fun x => by simp [tens]
    rw [this, map_zero]

theorem actsD_zero {R κ : Type} [Zero R] [Fintype κ] (ev : AF F → R) (T : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) :
    ActsD ev (fun t => T t) 0 0 := fun r _ x => by
  have : tens ev 0 r = 0 := funext fun x => by simp [tens]
  simp only [this, map_zero]
  exact hasDerivAt_const _ _

theorem augAt_le (v : Pl F) : augAt om v ≤ SB _ := Submodule.span_le.2 (by
  rintro _ ⟨g, -, x, hx, y, hy, -, rfl⟩
  exact sub_mem hy hx)

theorem one_at' {m : ℕ} {Y : Spc F E m} {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ Y.J) ∈ UAt σ Y ev :=
  fun u _ => by simp [mat]

theorem ex_fin (hp : IsPair B M χX χW om r s r' s') (v : Pl F) (h : UAt σ W (evFin F v)) :
    ∀ x ∈ SB (Fin n × Fin d → Fv F v), ∃ y, y ∈ SB _ ∧ Acts (evFin F v) (om (1, h.1)) x y := fun x hx => by
  obtain ⟨ω, ρ, hω⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ n d B X W M om
    ⟨hp.base, ⟨_, _, hp.herm⟩, ⟨_, _, hp.skew⟩, hp.good, ⟨_, _, hp.weil⟩⟩ v
  exact ⟨_, hω.pres 1 (one_at' _) h h.2 x hx, (hω.acts 1 (one_at' _) h h.2 x hx _).2 rfl⟩

def RInf (B : Base F E) (om : Rep σ X W) : Lines σ W ⊕ KInf σ W B.emb → SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d) → Prop
  | .inl γ, f, g => ActsD (evI F) (fun t => om (1, γ.1 (Multiplicative.ofAdd t))) f g
  | .inr k, f, g => Acts (evI F) (om (1, k.1)) f g

theorem kinf_one {m : ℕ} {Y : Spc F E m} (τ) : (1 : UA σ Y.J) ∈ KInf σ Y τ :=
  ⟨one_at' _, fun w => by
    have : (mat (1 : UA σ Y.J)).map (piInf (τ w)) = 1 := by simp [mat]
    rw [this]; exact Commute.one_left _⟩

theorem pol_lie (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s') {γ δ} (hγ : γ ∈ Lines σ X)
    (hδ : δ ∈ Lines σ W) {f} (hf : f ∈ M.Pol B.ψ B.emb) :
    ∃ g ∈ M.Pol B.ψ B.emb, ∀ g' : SInf F _,
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), δ (Multiplicative.ofAdd t))) f g' ↔ g' = g := by
  choose op hop _ using hO F E σ B n d X W M χX χW om r s r' s' hp
  obtain ⟨g, h1, h2, -⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp γ hγ δ hδ (fun t => op _ (hγ.2 _) _ (hδ.2 _))
    (fun t => hop _ _ _ _) f hf
  exact ⟨g, h1, fun g' => ⟨fun h => (hQ F _ f g' g).2 _ h h2, fun h => h ▸ h2⟩⟩

theorem pol_k (hO : ArchOp) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s') {k k'} (hk : k ∈ KInf σ X B.emb)
    (hk' : k' ∈ KInf σ W B.emb) {f} (hf : f ∈ M.Pol B.ψ B.emb) :
    ∃ g ∈ M.Pol B.ψ B.emb, ∀ g' : SInf F _, Acts (evI F) (om (k, k')) f g' ↔ g' = g := by
  obtain ⟨T, h1, h2⟩ := hO F E σ B n d X W M χX χW om r s r' s' hp k hk.1 k' hk'.1
  exact ⟨T f, h2 hk hk' f hf, fun g' => ⟨fun h => (hQ F _ f g' _).1 _ h (h1.2 f), fun h => h ▸ h1.2 f⟩⟩

theorem rinf_ex (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s') (i) {f}
    (hf : f ∈ M.Pol B.ψ B.emb) : ∃ g ∈ M.Pol B.ψ B.emb, ∀ g', RInf B om i f g' ↔ g' = g := by
  rcases i with γ | k
  · exact pol_lie hO hL hQ hp (γ := 1) ⟨continuous_const, fun _ => one_at' _⟩ γ.2 hf
  · exact pol_k hO hQ hp (kinf_one _) k.2 hf

theorem rinf_zero (i) : RInf B om i 0 0 := by
  rcases i with γ | k
  · exact actsD_zero _ fun t => om (1, γ.1 (Multiplicative.ofAdd t))
  · exact acts_zero _ _

theorem max_fin {P : Type} [AddCommGroup P] [Module ℂ P] [Nontrivial P] {v : Pl F} {p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P}
    (on : (SB _).map p = ⊤) (inv : augAt om v ≤ LinearMap.ker p)
    (h : (∀ i : UAt σ W (evFin F v), ∀ x ∈ SB _, ∀ y, y ∈ SB _ ∧ Acts (evFin F v) (om (1, i.1)) x y → p x = 0 → p y = 0) ∧
      ∀ N ≤ SB _, (∀ i : UAt σ W (evFin F v), ∀ x ∈ N, ∀ y, y ∈ SB _ ∧ Acts (evFin F v) (om (1, i.1)) x y → y ∈ N) →
        N.map p = ⊥ ∨ N.map p = ⊤) :
    Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) (LinearMap.ker p ⊓ SB _) :=
  maximal_of p _ _ on (fun _ h => h.2.1)
    ⟨le_inf inv (augAt_le v), inf_le_right, fun g hg x hx y hy e => ⟨h.1 ⟨g, hg⟩ x hx.2 y ⟨hy, e⟩ hx.1, hy⟩⟩
    fun N hN => h.2 N hN.2.1 fun i x hx y hy => hN.2.2 i i.2 x hx y hy.1 hy.2

theorem max_inf (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s') {P : Type} [AddCommGroup P]
    [Module ℂ P] [Nontrivial P] {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P} (q : RealQuot B M om p)
    (h : (∀ i, ∀ x ∈ M.Pol B.ψ B.emb, ∀ y, RInf B om i x y → p x = 0 → p y = 0) ∧
      ∀ N ≤ M.Pol B.ψ B.emb, (∀ i, ∀ x ∈ N, ∀ y, RInf B om i x y → y ∈ N) → N.map p = ⊥ ∨ N.map p = ⊤) :
    Maximal (fun P => GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P ∧ P ≠ M.Pol B.ψ B.emb) (LinearMap.ker p ⊓ M.Pol B.ψ B.emb) := by
  have st : ∀ i, ∀ x ∈ LinearMap.ker p ⊓ M.Pol B.ψ B.emb, ∀ y, RInf B om i x y → y ∈ LinearMap.ker p ⊓ M.Pol B.ψ B.emb :=
    fun i x hx y hy => by
      obtain ⟨g, hg, e⟩ := rinf_ex hO hL hQ hp i hx.2
      exact ⟨h.1 i x hx.2 y hy hx.1, (e y).1 hy ▸ hg⟩
  refine maximal_of p _ _ q.onto (fun _ h => h.1) ⟨inf_le_right, fun γ hγ f hf y hy => ⟨q.lie γ hγ f hf y hy, ?_⟩,
    fun k hk f hf y hy => ⟨show p (y - f) = 0 by rw [map_sub, q.cpt k hk f hf y hy, sub_self], ?_⟩,
    fun γ hγ f hf y hy => st (.inl ⟨γ, hγ⟩) f hf y hy, fun k hk f hf y hy => st (.inr ⟨k, hk⟩) f hf y hy⟩
    fun N hN => h.2 N hN.1 ?_
  · obtain ⟨g, hg, e⟩ := pol_lie hO hL hQ hp hγ (δ := 1) ⟨continuous_const, fun _ => one_at' _⟩ hf
    exact (e y).1 hy ▸ hg
  · obtain ⟨g, hg, e⟩ := pol_k hO hQ hp hk (kinf_one _) hf
    exact sub_mem ((e y).1 hy ▸ hg) hf
  · rintro (γ | k) x hx y hy
    exacts [hN.2.2.2.1 γ γ.2 x hx y hy, hN.2.2.2.2 k k.2 x hx y hy]

end Pair

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem maxFinP (m : IsMatched B G X om om' R Rf) (v : Pl F) :
    Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) (LinearMap.ker (Rf.p v) ⊓ SB _) ∧
      Maximal (fun P => GlobalTheory.Published.ThetaSub om' v P ∧ P ≠ SB _) (LinearMap.ker (Rf.p' v) ⊓ SB _) := by
  haveI := m.fin.nontriv v
  have hecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
    ⟨h.1.div' h'.1, fun x => by rw [MonoidHom.div_apply, h.2, h'.2, div_one]⟩
  have res_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {n k l : ℕ}
      (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' k) (e : l = n + k) : ResEtaPow K (χ / χ') l := by
    intro x
    rw [MonoidHom.div_apply, Circle.coe_div, h, h', e]
    split_ifs
    · simp
    · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]
  have p1 : IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨m.triple.base, m.triple.geo.hV, m.triple.geo.hW, m.triple.geo.hM, m.triple.chars.heckeβ,
      hecke_div m.triple.chars.heckeβ m.triple.chars.heckeα, m.triple.chars.resβ,
      res_div m.triple.chars.resβ m.triple.chars.resα rfl, m.triple.weil⟩
  have p2 : IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨m.triple.base, m.triple.geo.hV', m.triple.geo.hW, m.triple.geo.hM', m.triple.chars.heckeα,
      hecke_div m.triple.chars.heckeα m.triple.chars.heckeβ, m.triple.chars.resα,
      res_div m.triple.chars.resα m.triple.chars.resβ (add_comm _ _), m.triple.weil'⟩
  have := absMax (R := fun (i : UAt σ G.W (evFin F v)) x y => y ∈ SB _ ∧ Acts (evFin F v) (om (1, i.1)) x y)
    (R' := fun (i : UAt σ G.W (evFin F v)) x y => y ∈ SB _ ∧ Acts (evFin F v) (om' (1, i.1)) x y) (m.fin.onto v) (m.fin.onto' v)
    (ex_fin p1 v) (ex_fin p2 v)
    (fun _ => ⟨zero_mem _, acts_zero _ _⟩) (fun _ => ⟨zero_mem _, acts_zero _ _⟩)
    (fun i x hx x' hx' y y' h h' => m.fin.equiv v i i.2 x hx x' hx' y h.1 y' h'.1 h.2 h'.2)
    fun N hN => m.fin.irred v N fun h hh x hx y hy e => hN ⟨h, hh⟩ x hx y ⟨hy, e⟩
  exact ⟨max_fin (m.fin.onto v) (m.fin.inv v) this.1, max_fin (m.fin.onto' v) (m.fin.inv' v) this.2⟩

theorem maxInfP (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (m : IsMatched B G X om om' R Rf) :
    Maximal (fun P => GlobalTheory.Published.ThetaSubInf G.M B.ψ B.emb om P ∧ P ≠ G.M.Pol B.ψ B.emb)
        (LinearMap.ker R.p ⊓ G.M.Pol B.ψ B.emb) ∧
      Maximal (fun P => GlobalTheory.Published.ThetaSubInf G.M' B.ψ B.emb om' P ∧ P ≠ G.M'.Pol B.ψ B.emb)
        (LinearMap.ker R.p' ⊓ G.M'.Pol B.ψ B.emb) := by
  haveI := m.real.nontriv
  have hecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
    ⟨h.1.div' h'.1, fun x => by rw [MonoidHom.div_apply, h.2, h'.2, div_one]⟩
  have res_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {n k l : ℕ}
      (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' k) (e : l = n + k) : ResEtaPow K (χ / χ') l := by
    intro x
    rw [MonoidHom.div_apply, Circle.coe_div, h, h', e]
    split_ifs
    · simp
    · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]
  have p1 : IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨m.triple.base, m.triple.geo.hV, m.triple.geo.hW, m.triple.geo.hM, m.triple.chars.heckeβ,
      hecke_div m.triple.chars.heckeβ m.triple.chars.heckeα, m.triple.chars.resβ,
      res_div m.triple.chars.resβ m.triple.chars.resα rfl, m.triple.weil⟩
  have p2 : IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨m.triple.base, m.triple.geo.hV', m.triple.geo.hW, m.triple.geo.hM', m.triple.chars.heckeα,
      hecke_div m.triple.chars.heckeα m.triple.chars.heckeβ, m.triple.chars.resα,
      res_div m.triple.chars.resα m.triple.chars.resβ (add_comm _ _), m.triple.weil'⟩
  have := absMax (R := RInf B om) (R' := RInf B om') m.real.quot.onto m.real.quot'.onto
    (fun i x hx => let ⟨g, _, e⟩ := rinf_ex hO hL hQ p1 i hx; ⟨g, (e g).2 rfl⟩)
    (fun i x hx => let ⟨g, _, e⟩ := rinf_ex hO hL hQ p2 i hx; ⟨g, (e g).2 rfl⟩) rinf_zero rinf_zero
    (by
      rintro (γ | k) x hx x' hx' y y' h h'
      exacts [m.real.lie γ γ.2 x hx x' hx' y y' h h', m.real.cpt k k.2 x hx x' hx' y y' h h'])
    fun N hN => m.real.irred N (fun γ hγ => hN (.inl ⟨γ, hγ⟩)) fun k hk => hN (.inr ⟨k, hk⟩)
  exact ⟨max_inf hO hL hQ p1 m.real.quot this.1, max_inf hO hL hQ p2 m.real.quot' this.2⟩

end PositivityTheory.ThKF

end
end

-- bundled from Development.WeilBound.ThetaLifts.CartanFactorisation.UpdSelf
section
noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped ComplexConjugate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
  {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

def upd {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x : (κ → Fv F v) → ℂ) : ∀ u : Pl F, (κ → Fv F u) → ℂ := by
  classical exact Function.update φ v x

theorem upd_self {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x) : upd φ v x v = x := by
  classical exact Function.update_self ..

theorem upd_ne {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x) {u} (h : u ≠ v) : upd φ v x u = φ u := by
  classical exact Function.update_of_ne h ..

theorem upd_eq {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) : upd φ v (φ v) = φ := by
  classical exact Function.update_eq_self ..

theorem upd_upd {κ : Type} (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x y) : upd (upd φ v x) v y = upd φ v y := by
  classical exact Function.update_idem ..

theorem upd_sb {κ : Type} [Fintype κ] {φ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h : ∀ u, φ u ∈ SB _) {v : Pl F} {x} (hx : x ∈ SB _) (u) :
    upd φ v x u ∈ SB _ := by
  by_cases e : u = v
  · subst e; rwa [upd_self]
  · rw [upd_ne _ _ _ e]; exact h u

theorem upd_cof {κ : Type} {φ ψ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h : ∀ᶠ u in cofinite, φ u = ψ u) (v : Pl F) (x) :
    ∀ᶠ u in cofinite, upd φ v x u = ψ u :=
  (h.and (Filter.eventually_cofinite_ne v)).mono fun _ hu => (upd_ne _ _ _ hu.2).trans hu.1

theorem intersection_update_fsHerm_neg_one (hP : PureAct) (hp : IsPair B M χX χW om r s r' s') (f : SInf F (Fin n × Fin d)) {φ} (h1 : ∀ u, φ u ∈ SB _)
    (h2 : ∀ᶠ u in cofinite, φ u = M.vac u) (v : Pl F) :
    ∃ j : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] Fn F n d, (∀ x, j x = pure f (upd φ v x)) ∧
      ∀ S, ∀ x ∈ SB _, ∀ y, Acts (evFin F v) S x y → S (j x) = j y := by
  have h3 := (h2.and hp.good.std).mono fun _ h => h.1.trans h.2
  have l : ∀ x y (a : ℂ), pure f (upd φ v (x + a • y)) = pure f (upd φ v x) + a • pure f (upd φ v y) :=
    (hP F _ v id f φ h1 h3).2.1
  have z : pure f (upd φ v 0) = 0 := by
    have := l 0 0 1
    simp only [one_smul, add_zero] at this
    exact left_eq_add.1 this
  refine ⟨{ toFun := fun x => pure f (upd φ v x)
            map_add' := fun x y => by simpa using l x y 1
            map_smul' := fun c x => by
              have := l 0 x c
              rwa [zero_add, z, zero_add] at this },
    fun _ => rfl, fun S x hx y hxy => ?_⟩
  have := (hP F _ v S f (upd φ v x) (upd_sb h1 hx) (upd_cof h3 v x)).2.2 y (by rwa [upd_self])
  exact this.trans (congrArg (pure f) (upd_upd φ v x y))

end PositivityTheory.ThKF

end
end

