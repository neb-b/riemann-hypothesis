module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.GelOfHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.EigArch

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.HeckeFunctionOneMul
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

private theorem heckeFunction_mul (w : Pl E) (x y : Ex (Fin (a + 1) × Fin (b + 1))) :
    fn2 a b w (x.mul y) = PositivityTheory.Rg.BcN.F2.mconv (fn2 a b w x) (fn2 a b w y) := by
  funext m
  simp only [fn2, Ex.fn, PositivityTheory.Rg.BcN.F2.mconv]

private theorem heckeFunction_one (w : Pl E) :
    fn2 a b w (.one : Ex (Fin (a + 1) × Fin (b + 1))) = (K2 a b w : Set _).indicator 1 := rfl

private theorem heckeFunction_mul_one {Z : Finset (Pl E)} (L : Lv a b Z) (w : Pl E) (x : Ex (Fin (a + 1) × Fin (b + 1))) :
    fn2 a b w (x.mul .one) = fn2 a b w x := by
  rw [heckeFunction_mul, heckeFunction_one]
  exact ((locAlg E a b Z L w).2.2.2.2 _ (Asm.exHecke2 E a b w x)).1

private theorem heckeFunction_one_mul {Z : Finset (Pl E)} (L : Lv a b Z) (w : Pl E) (x : Ex (Fin (a + 1) × Fin (b + 1))) :
    fn2 a b w (Ex.one.mul x) = fn2 a b w x := by
  rw [heckeFunction_mul, heckeFunction_one]
  exact ((locAlg E a b Z L w).2.2.2.2 _ (Asm.exHecke2 E a b w x)).2.1

private theorem position_congr {Z : Finset (Pl E)} (φ : ∀ w : Pl E, LF a b w) {w : Pl E}
    {e e' : Pl E → Ex (Fin (a + 1) × Fin (b + 1))} (h : fn2 a b w (e w) = fn2 a b w (e' w)) :
    intersection_update_fsHerm_neg_one Z {w} φ e = intersection_update_fsHerm_neg_one Z {w} φ e' := by
  funext x
  unfold intersection_update_fsHerm_neg_one
  by_cases hx : x = w
  · subst hx
    simp [h]
  · simp [hx]

end

theorem hkVal : HkVal := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ f t₁ t₂ T e₁ e₂ hT hd hc hlv hev
  obtain ⟨-, -, -, hone, hemp, hfx, hfin, hins⟩ := hkMul E a b l₁ l₂ D A S Z L hS hZ
  have hCM : ∀ ψ ψ' : Matrix Unit Unit (Hf E a b → ℂ), IsFinM ψ → IsFinM ψ' →
      convF A.ν (mulF A.ν ψ ψ') f = convF A.ν ψ (convF A.ν ψ' f) ∧
      convF A.ν (ψ + ψ') f = convF A.ν ψ f + convF A.ν ψ' f ∧
      ∀ c : ℂ, convF A.ν (c • ψ) f = c • convF A.ν ψ f ∧ convF A.ν ψ (c • f) = c • convF A.ν ψ f :=
    (convMul E A.blk f hc).2
  have hfix : convF A.ν (A.idm S L) f = f := (idmAct E a b l₁ l₂ D A S Z L hS hZ).2.2 f hlv
  have hln : L.Fix L.ln := (positionTest E a b S Z L hZ).1
  have hmul : ∀ (T : Finset (Pl E)) (x₁ x₂ y₁ y₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))),
      mulF A.ν (A.hk S L T x₁ x₂) (A.hk S L T y₁ y₂) =
        A.hk S L T (fun w => (x₁ w).mul (y₁ w)) (fun w => (x₂ w).mul (y₂ w)) :=
    fun T x₁ x₂ y₁ y₂ => (hfx T L.ln x₁ x₂ hln).2.2 y₁ y₂
  have hact : ∀ (ψ ψ' : Matrix Unit Unit (Hf E a b → ℂ)) (c c' : ℂ), IsFinM ψ → IsFinM ψ' →
      convF A.ν ψ f = c • f → convF A.ν ψ' f = c' • f → convF A.ν (mulF A.ν ψ ψ') f = (c * c') • f := by
    intro ψ ψ' c c' h h' hc₁ hc₂
    rw [(hCM ψ ψ' h h').1, hc₂, ((hCM ψ ψ' h h').2.2 c').2, hc₁, smul_smul, mul_comm]
  have hcg : ∀ (w : Pl E) (x₁ x₂ y₁ y₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))),
      fn2 a b w (x₁ w) = fn2 a b w (y₁ w) → fn2 a b w (x₂ w) = fn2 a b w (y₂ w) →
      A.hk S L {w} x₁ x₂ = A.hk S L {w} y₁ y₂ := by
    intro w x₁ x₂ y₁ y₂ h₁ h₂
    show A.ff S (intersection_update_fsHerm_neg_one Z {w} L.ln x₁) (intersection_update_fsHerm_neg_one Z {w} L.ln x₂) = A.ff S (intersection_update_fsHerm_neg_one Z {w} L.ln y₁) (intersection_update_fsHerm_neg_one Z {w} L.ln y₂)
    rw [position_congr L.ln h₁, position_congr L.ln h₂]
  have hone' : ∀ w : Pl E, convF A.ν (A.hk S L {w} (fun _ => .one) (fun _ => .one)) f = f := by
    intro w
    rw [hone, hfix]
  have left : ∀ w ∈ T, ∀ x : Ex (Fin (a + 1) × Fin (b + 1)),
      convF A.ν (A.hk S L {w} (fun _ => x) (fun _ => .one)) f = x.ev (t₁ w) • f := by
    intro w hw x
    have hwS : w ∈ S := hT.1 w hw
    have hwZ : w ∉ Z := Finset.disjoint_left.1 hd hw
    have hl := fun x y z c => hkLin E a b l₁ l₂ D A S Z L hS hZ w hwS hwZ x y z c
    induction x with
    | one => rw [hone' w]; simp [Ex.ev]
    | gen p => simpa [Ar.hk1, Ex.ev] using (hev w hw p).1
    | smul c x ih =>
      rw [(hl x x .one c).2.1, ((hCM _ _ (hfin {w} (fun _ => x) (fun _ => .one)).1
        (hfin {w} (fun _ => x) (fun _ => .one)).1).2.2 c).1, ih, smul_smul]
      rfl
    | add x y ihx ihy =>
      rw [(hl x y .one 0).1, (hCM _ _ (hfin {w} (fun _ => x) (fun _ => .one)).1
        (hfin {w} (fun _ => y) (fun _ => .one)).1).2.1, ihx, ihy, ← add_smul]
      rfl
    | mul x y ihx ihy =>
      have h := hact _ _ _ _ (hfin _ _ _).1 (hfin _ _ _).1 ihx ihy
      rw [hmul, hcg w (fun w => (fun _ => x) w |>.mul ((fun _ => y) w))
        (fun w => (Ex.one).mul .one) (fun _ => x.mul y) (fun _ => .one) rfl (heckeFunction_mul_one L w .one)] at h
      exact h
  have right : ∀ w ∈ T, IsSplitAt w → ∀ y : Ex (Fin (a + 1) × Fin (b + 1)),
      convF A.ν (A.hk S L {w} (fun _ => .one) (fun _ => y)) f = y.ev (t₂ w) • f := by
    intro w hw hsp y
    have hwS : w ∈ S := hT.1 w hw
    have hwZ : w ∉ Z := Finset.disjoint_left.1 hd hw
    have hl := fun x y z c => (hkLin E a b l₁ l₂ D A S Z L hS hZ w hwS hwZ x y z c).2.2.1 hsp
    induction y with
    | one => rw [hone' w]; simp [Ex.ev]
    | gen p => simpa [Ar.hk1, Ex.ev] using (hev w hw p).2 hsp
    | smul c x ih =>
      rw [(hl x x .one c).2, ((hCM _ _ (hfin {w} (fun _ => .one) (fun _ => x)).1
        (hfin {w} (fun _ => .one) (fun _ => x)).1).2.2 c).1, ih, smul_smul]
      rfl
    | add x y ihx ihy =>
      rw [(hl x y .one 0).1, (hCM _ _ (hfin {w} (fun _ => .one) (fun _ => x)).1
        (hfin {w} (fun _ => .one) (fun _ => y)).1).2.1, ihx, ihy, ← add_smul]
      rfl
    | mul x y ihx ihy =>
      have h := hact _ _ _ _ (hfin _ _ _).1 (hfin _ _ _).1 ihx ihy
      rw [hmul, hcg w (fun w => (Ex.one).mul .one) (fun w => (fun _ => x) w |>.mul ((fun _ => y) w))
        (fun _ => .one) (fun _ => x.mul y) (heckeFunction_mul_one L w .one) rfl] at h
      exact h
  have place : ∀ w ∈ T, convF A.ν (A.hk S L {w} e₁ e₂) f = ((e₁ w).ev (t₁ w) * (e₂ w).ev (t₂ w)) • f := by
    intro w hw
    by_cases hsp : IsSplitAt w
    · have h := hact _ _ _ _ (hfin {w} (fun _ => e₁ w) (fun _ => .one)).1
        (hfin {w} (fun _ => .one) (fun _ => e₂ w)).1 (left w hw (e₁ w)) (right w hw hsp (e₂ w))
      rw [hmul, hcg w _ _ e₁ e₂ (heckeFunction_mul_one L w (e₁ w)) (heckeFunction_one_mul L w (e₂ w))] at h
      exact h
    · have hwS : w ∈ S := hT.1 w hw
      have hwZ : w ∉ Z := Finset.disjoint_left.1 hd hw
      have h₁ : A.hk S L {w} e₁ e₂ = A.hk S L {w} (fun _ => e₁ w) (fun _ => .one) :=
        (hcg w e₁ e₂ (fun _ => e₁ w) (fun _ => e₂ w) rfl rfl).trans
          ((hkLin E a b l₁ l₂ D A S Z L hS hZ w hwS hwZ (e₂ w) .one (e₁ w) 0).2.2.2 hsp)
      rw [h₁, left w hw (e₁ w), hT.2 w hw hsp, mul_one]
  have all : ∀ T' : Finset (Pl E), T' ⊆ T →
      convF A.ν (A.hk S L T' e₁ e₂) f = (∏ w ∈ T', (e₁ w).ev (t₁ w) * (e₂ w).ev (t₂ w)) • f := by
    intro T'
    refine Finset.induction_on T' ?_ ?_
    · intro _
      rw [hemp, hfix]
      simp
    · intro w T'' hw ih hsub
      have hwT : w ∈ T := hsub (Finset.mem_insert_self w T'')
      rw [hins T'' w e₁ e₂ hw, Finset.prod_insert hw]
      exact hact _ _ _ _ (hfin _ _ _).1 (hfin _ _ _).1 (place w hwT)
        (ih fun x hx => hsub (Finset.mem_insert_of_mem hx))
  exact all T subset_rfl

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PackStep
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem slice_left {X Y : Type} (W₁ : Submodule ℂ (X → ℂ)) (W₂ : Submodule ℂ (Y → ℂ)) (y : Y) (F : X × Y → ℂ)
    (h : F ∈ Submodule.span ℂ {f : X × Y → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :
    (fun x => F (x, y)) ∈ W₁ := by
  induction h using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨w₁, h₁, w₂, _, rfl⟩ := hg
    have := W₁.smul_mem (w₂ y) h₁
    convert this using 1
    funext x
    simp [mul_comm]
  | zero => exact W₁.zero_mem
  | add g g' _ _ hg hg' => exact W₁.add_mem hg hg'
  | smul c g _ hg => exact W₁.smul_mem c hg

private theorem slice_right {X Y : Type} (W₁ : Submodule ℂ (X → ℂ)) (W₂ : Submodule ℂ (Y → ℂ)) (x : X) (F : X × Y → ℂ)
    (h : F ∈ Submodule.span ℂ {f : X × Y → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :
    (fun y => F (x, y)) ∈ W₂ := by
  induction h using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨w₁, _, w₂, h₂, rfl⟩ := hg
    exact W₂.smul_mem (w₁ x) h₂
  | zero => exact W₂.zero_mem
  | add g g' _ _ hg hg' => exact W₂.add_mem hg hg'
  | smul c g _ hg => exact W₂.smul_mem c hg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

private theorem type_left {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ} (h : TypeH K₁ K₂ W₁ W₂ F)
    (m₂ : GA E b) (φ : Sm E a) (hφ : φ.1 = fun x => F (x, m₂)) : TypeB K₁ W₁ φ := by
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · rw [hφ]
    simpa using h.1 u hu 1 K₂.one_mem (g, m₂)
  · rw [hφ]
    simpa using slice_left W₁ W₂ 1 _ (h.2 (g, m₂))

private theorem type_right {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ} (h : TypeH K₁ K₂ W₁ W₂ F)
    (m₁ : GA E a) (φ : Sm E b) (hφ : φ.1 = fun x => F (m₁, x)) : TypeB K₂ W₂ φ := by
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · rw [hφ]
    simpa using h.1 1 K₁.one_mem u hu (m₁, g)
  · rw [hφ]
    simpa using slice_right W₁ W₂ 1 _ (h.2 (m₁, g))

private theorem gen_a {l₁ : InfinitePlace E → DomWeight a} {l₂ : InfinitePlace E → DomWeight b} {D : Dom E a b} (A : Ar l₁ l₂ D)
    (S : Set (Pl E)) {Z : Finset (Pl E)} (L : Lv a b Z) (T : Finset (Pl E)) (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1)))
    (v : InfinitePlace E) (r : Bool) (m : ℕ) :
    (A.gen S L T e₁ e₂ (.inr (.inl (v, r, m, false)))).Φ =
      tens (Function.update (A.ka []) v (A.ka [(r, m)] v)) (A.kb []) (A.idm S L) := by
  have h1 : (fun w => A.ka (if w = v ∧ false = false then [(r, m)] else []) w) = Function.update (A.ka []) v (A.ka [(r, m)] v) := by
    funext w
    by_cases h : w = v
    · subst h
      simp
    · simp [h]
  have h2 : (fun w => A.kb (if w = v ∧ false = true then [(r, m)] else []) w) = A.kb [] := by
    funext w
    simp
  rw [← h1, ← h2]
  rfl

private theorem gen_b {l₁ : InfinitePlace E → DomWeight a} {l₂ : InfinitePlace E → DomWeight b} {D : Dom E a b} (A : Ar l₁ l₂ D)
    (S : Set (Pl E)) {Z : Finset (Pl E)} (L : Lv a b Z) (T : Finset (Pl E)) (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1)))
    (v : InfinitePlace E) (r : Bool) (m : ℕ) :
    (A.gen S L T e₁ e₂ (.inr (.inl (v, r, m, true)))).Φ =
      tens (A.ka []) (Function.update (A.kb []) v (A.kb [(r, m)] v)) (A.idm S L) := by
  have h1 : (fun w => A.kb (if w = v ∧ true = true then [(r, m)] else []) w) = Function.update (A.kb []) v (A.kb [(r, m)] v) := by
    funext w
    by_cases h : w = v
    · subst h
      simp
    · simp [h]
  have h2 : (fun w => A.ka (if w = v ∧ true = false then [(r, m)] else []) w) = A.ka [] := by
    funext w
    simp
  rw [← h1, ← h2]
  rfl

theorem packStep : PackStep := by
  intro E _ _ _ a b l₁ l₂
  obtain ⟨W₁, W₂, f₁, f₂, hW⟩ := PositivityTheory.Rg.BcB.CG.pack_holds E a b (Ml l₁) (Ml l₂)
  refine ⟨W₁, W₂, f₁, f₂, ?_⟩
  intro D A S Z L hS hZ T e₁ e₂ s f hs hE
  haveI := A.ha
  haveI := A.hb
  haveI := A.hν
  haveI : BorelSpace (G a) := ⟨rfl⟩
  haveI : BorelSpace (G b) := ⟨rfl⟩
  haveI : BorelSpace (Hf E a b) := ⟨rfl⟩
  obtain ⟨-, -, hOk, -, -⟩ := ptOk E a b l₁ l₂ D A
  obtain ⟨hψ, -, -, -, -, -, hhk, -⟩ := hkMul E a b l₁ l₂ D A S Z L hS hZ
  obtain ⟨hlev, -, hfix⟩ := idmAct E a b l₁ l₂ D A S Z L hS hZ
  have hK₁ := kgFacts E a S Z L.L₁ hS hZ (fun w => ⟨L.open₁ w, L.le₁ w⟩) (fun w hw => (L.off w hw).1)
  have hK₂ := kgFacts E b S Z L.L₂ hS hZ (fun w => ⟨L.open₂ w, L.le₂ w⟩) (fun w hw => (L.off w hw).2)
  have h0 := hOk (fun _ => []) (fun _ => []) (A.idm S L) hψ
  have hka : IsMults A.μa (A.ka []) (fun v => A.valW []) A.T := h0.ka
  have hkb : IsMults A.μb (A.kb []) (fun v => A.valW []) A.T := h0.kb
  have he : PositivityTheory.Rg.BcB.E.conv D.μ (tens (A.ka []) (A.kb []) (A.idm S L)) f = s (.inl ()) • f := hE.eig (.inl ())
  have hea : ∀ v r m, PositivityTheory.Rg.BcB.E.conv D.μ (tens (Function.update (A.ka []) v (A.ka [(r, m)] v)) (A.kb []) (A.idm S L)) f =
      s (.inr (.inl (v, r, m, false))) • f := fun v r m => by
    have h1 := hE.eig (.inr (.inl (v, r, m, false)))
    rw [gen_a] at h1
    exact h1
  have heb : ∀ v r m, PositivityTheory.Rg.BcB.E.conv D.μ (tens (A.ka []) (Function.update (A.kb []) v (A.kb [(r, m)] v)) (A.idm S L)) f =
      s (.inr (.inl (v, r, m, true))) • f := fun v r m => by
    have h1 := hE.eig (.inr (.inl (v, r, m, true)))
    rw [gen_b] at h1
    exact h1
  obtain ⟨M, hM⟩ := hE.wl
  obtain ⟨χa, χb, ga, gb, hEig, hty, s₁, s₂, au₁, au₂, ic₁, ic₂⟩ :=
    hW D A.μa A.μb A.ν Unit (A.ka []) (A.kb []) (fun v => A.valW []) (fun v => A.valW []) A.T (A.idm S L) A.bump
      (fun r m => A.ka [(r, m)]) (fun r m => A.kb [(r, m)]) (Kg S L.L₁) (Kg S L.L₂) M f (s (.inl ()))
      (fun v r m => s (.inr (.inl (v, r, m, false)))) (fun v r m => s (.inr (.inl (v, r, m, true)))) A.compat hka hkb hψ A.isBump
      (A.kera []) (A.kerb []) (fun r m v => A.kera [(r, m)] v) (fun r m v => A.kerb [(r, m)] v) hK₁.1 hK₂.1 hlev hE.cont hE.ne
      hE.inv hM hs he hea heb
  have hlevel : LevelF (Kg S L.L₁) (Kg S L.L₂) f := fun i u₁ h₁ u₂ h₂ x => (hty i).1 u₁ h₁ u₂ h₂ x
  have hR : Repr D (A.ka []) (A.kb []) (A.idm S L) f := ⟨hE.cont, s (.inl ()), hs, he⟩
  have hact : ∀ ψ', IsFinM ψ' → PositivityTheory.Rg.BcB.E.conv D.μ (tens (A.ka []) (A.kb []) ψ') f =
      (valA (fun v => A.valW []) χa * valA (fun v => A.valW []) χb) • convF A.ν ψ' f := fun ψ' h' =>
    actVal_holds E a b D A.μa A.μb A.ν (Ml l₁) (Ml l₂) Unit (A.ka []) (A.ka []) (A.kb []) (A.kb []) _ _ _ _ A.T A.T (A.idm S L) ψ' f
      χa χb A.compat hka hkb hψ hR ⟨s₁, s₂⟩ hEig hka hkb h'
  have hval : valA (fun v => A.valW []) χa * valA (fun v => A.valW []) χb = s (.inl ()) := by
    have h1 := hact _ hψ
    rw [he, hfix f hlevel] at h1
    exact (smul_left_injective ℂ hE.ne h1).symm
  have hfin : ∀ ψ' c', IsFinM ψ' → PositivityTheory.Rg.BcB.E.conv D.μ (tens (A.ka []) (A.kb []) ψ') f = c' • f →
      convF A.ν ψ' f = (c' / s (.inl ())) • f := fun ψ' c' h' e' => by
    have h1 := hact ψ' h'
    rw [e', hval] at h1
    have h2 : convF A.ν ψ' f = (s (.inl ()))⁻¹ • (s (.inl ()) • convF A.ν ψ' f) := by
      rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
    rw [h2, ← h1, smul_smul, inv_mul_eq_div]
  refine ⟨χa, χb, ga, gb, hlevel, ⟨s₁, s₂⟩, ?_, ?_, ?_⟩
  · intro φ hφ
    obtain ⟨i, m₂, e⟩ := id hφ
    exact ⟨au₁ φ hφ, type_left (hty i) m₂ φ e, fun t => ⟨(ic₁ t).1, fun u => (ic₁ t).2 u φ (Submodule.subset_span hφ)⟩⟩
  · intro φ hφ
    obtain ⟨i, m₁, e⟩ := id hφ
    exact ⟨au₂ φ hφ, type_right (hty i) m₁ φ e, fun t => ⟨(ic₂ t).1, fun u => (ic₂ t).2 u φ (Submodule.subset_span hφ)⟩⟩
  · rintro (x | u)
    · exact hfin _ _ (hhk _ _ _).1 (hE.eig (.inr (.inr (.inl x))))
    · exact hfin _ _ (hhk _ _ _).1 (hE.eig (.inr (.inr (.inr u))))

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

