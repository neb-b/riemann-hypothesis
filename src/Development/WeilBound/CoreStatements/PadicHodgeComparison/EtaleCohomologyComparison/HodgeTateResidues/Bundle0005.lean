module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle0003
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle0002
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Same
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.GammaIndependence.PullRId
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.EtDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.TowerSmulZero
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.CompId
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT.H2

open Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {Y : CB l K}


open Classical in
def coL {m : ℕ} (L : Lv Y m) (M : Model l K) (r j : ℕ) : HG (L.QB M) r j →+ ∀ a, Module.Dual K (Hdg M.q a j) →+ ℂ_[l] :=
  if h : ∃ co, IsCo L.γB M.q (L.QB M) L.θ L.tB_mem r j co then h.choose else 0

theorem isCo (hC : CoEx l K) {m : ℕ} (L : Lv Y m) {M : Model l K} (hM : M.Sm) {r : ℕ} (j : ℕ) (h : r < m) :
    IsCo L.γB M.q (L.QB M) L.θ L.tB_mem r j (coL L M r j) := by
  rw [coL, dite_eq_left (hC L M hM r j h).2]
  exact (hC L M hM r j h).2.choose_spec

theorem aCo (hC : CoEx l K) {m : ℕ} (L : Lv Y m) {M : Model l K} (hM : M.Sm) {r : ℕ} (j : ℕ) (h : r < m) :
    ACo (V := fun a => Hdg M.q a j) L.θ (fun a => L.μ M a r j) r (coL L M r j) :=
  ⟨(isCo hC L hM j h).smul, (isCo hC L hM j h).same, (isCo hC L hM j h).diff, (hC L M hM r j h).1⟩

def idH {m : ℕ} (L : Lv Y m) : LHom L L (RingHom.id _) (fun _ => RingHom.id _) (RingHom.id _) 1 where
  le := le_rfl
  sA := RingHom.id _
  sB := RingHom.id _
  dpA := (DPMorphism.id L.γ).isDPMorphism
  dpB := (DPMorphism.id L.γB).isDPMorphism
  oA _ := rfl
  oB _ := rfl
  ι _ := rfl
  lam _ := rfl
  cris _ _ := rfl
  θ _ := rfl
  cB := 1
  t := (one_mul _).symm
  θc := map_one _

theorem co_hom (hC : CoEx l K) (hμ : HomMu l K) {m m' : ℕ} {L : Lv Y m} {L' : Lv Y m'} {sΛ : Y.Λ →+* Y.Λ}
    {sn : ∀ n, Y.R n →+* Y.R n} {sC : ℂ_[l] →+* ℂ_[l]} {c : ℂ_[l]} (h : LHom L L' sΛ sn sC c) {M N : Model l K} (hM : M.Sm) (hN : N.Sm)
    (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) {r : ℕ} (j : ℕ) (hr : r < m') (w : HG (L.QB N) r j) (a : ℕ)
    (φ : Module.Dual K (Hdg M.q a j)) :
    coL L' M r j (h.fW u hu r j w) a φ =
      c ^ (r - a) * sC (coL L N r j w a (φ ∘ₗ pullH (Model.genMap u hu) (Model.genMap_q u hu) a j)) := by
  have := (aCo hC L hN j (hr.trans_le h.le)).hom (aCo hC L' hM j hr) le_rfl sC h.θ h.oB (h.fW u hu r j)
    (fun a => pullH (Model.genMap u hu) (Model.genMap_q u hu) a j) (fun a => h.cB ^ (r - a)) (fun a _ y => hμ h u hu a r j y) w a φ
  rw [map_pow, h.θc] at this
  exact this

def pullM (Y : CB l K) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) :
    GlobalTheory.LogCris.Mor (Y.L N n) (Y.L M n) (RingHom.id _) :=
  B.crMor (F := B.schFn N.p) (F' := B.schFn M.p) (b := Y.bs n) (b' := Y.bs n) (ht := rfl) (ht' := rfl) (RingHom.id _) rfl
    (DPMorphism.id _).isDPMorphism ((B.schMap u hu).ptK _) fun _ _ _ => rfl

theorem comp_id (hF : KForm) (M : Model l K) (h : 𝟙 M.X ≫ M.p = M.p) (a j : ℕ) (φ : Module.Dual K (Hdg M.q a j)) :
    φ ∘ₗ pullH (Model.genMap (𝟙 M.X) h) (Model.genMap_q _ h) a j = φ :=
  LinearMap.ext fun x => congrArg φ (hF.pull_id M.q _ _ (genMap_id M h) a j x)

theorem down (hC : CoEx l K) (hR : HomRho l K) (hμ : HomMu l K) (hF : KForm) {m m' : ℕ} {L : Lv Y m} {L' : Lv Y m'}
    (h : LHom L L' (RingHom.id _) (fun _ => RingHom.id _) (RingHom.id _) 1) {M : Model l K} (hM : M.Sm) {r j : ℕ} (hr : r < m')
    (x : Y.Fam M r j) (w : HG (L.QB M) r j) (hw : L.Rho x w) : ∃ w', L'.Rho x w' ∧ coL L' M r j w' = coL L M r j w := by
  have h1 := hR h (𝟙 M.X) (Category.id_comp _) (pullM Y (𝟙 M.X) (Category.id_comp _)) (fun _ _ _ => rfl) r j x w hw
  have e : (fun n => (pdOm (pullM Y (𝟙 M.X) (Category.id_comp _) n) (RingHom.id _) (h.cris n) r).pull j (x n)) = x :=
    funext fun n => pd_id (pullM Y (𝟙 M.X) (Category.id_comp _) n) (h.cris n) (fun _ => rfl)
      (fun B₀ y => Category.comp_id (show Spec B₀ ⟶ M.X from y.1.2)) r j (x n)
  rw [e] at h1
  refine ⟨_, h1, funext fun a => AddMonoidHom.ext fun φ => ?_⟩
  rw [co_hom hC hμ h hM hM _ _ j hr, comp_id hF, one_pow, one_mul]; rfl

variable (S : ∀ m, Lv Y (m + 1))


open Classical in
def gam {M : Model l K} {r j : ℕ} (x : Y.Fam M r j) : ∀ a, Module.Dual K (Hdg M.q a j) →+ ℂ_[l] :=
  if h : ∃ w, (S r).Rho x w then coL (S r) M r j h.choose else 0

variable {S}

structure Hyp (S : ∀ m, Lv Y (m + 1)) : Prop where
  ex : RhoEx l K
  co : CoEx l K
  hom : HomRho l K
  mu : HomMu l K
  mul : MulRho l K
  c1 : FirstChernHodgeTateCompat l K
  form : KForm
  dn : ∀ m, Nonempty (LHom (S (m + 1)) (S m) (RingHom.id _) (fun _ => RingHom.id _) (RingHom.id _) 1)

namespace Hyp
variable (H : Hyp S) {M : Model l K} (hM : M.Sm)
include H hM

theorem gam_eq {r j m : ℕ} (hm : r ≤ m) {x : Y.Fam M r j} (hx : CB.Comp x) {w : HG ((S m).QB M) r j} (hw : (S m).Rho x w) :
    gam S x = coL (S m) M r j w := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [gam, dite_eq_left ⟨w, hw⟩]
    exact congrArg _ ((H.ex.ex (S r) M hM r j r.lt_succ_self x hx).unique (Exists.choose_spec ⟨w, hw⟩) hw)
  | succ m hm ih =>
    obtain ⟨w', h1, h2⟩ := down H.co H.hom H.mu H.form (H.dn m).some hM (Nat.lt_succ_of_le hm) x w hw
    exact (ih h1).trans h2

theorem rho {r j m : ℕ} (hm : r ≤ m) {x : Y.Fam M r j} (hx : CB.Comp x) : ∃ w, (S m).Rho x w :=
  (H.ex.ex (S m) M hM r j (Nat.lt_succ_of_le hm) x hx).exists

theorem add {r j : ℕ} {x y : Y.Fam M r j} (hx : CB.Comp x) (hy : CB.Comp y) (hxy : CB.Comp (x + y)) (a : ℕ) :
    gam S (x + y) a = gam S x a + gam S y a := by
  obtain ⟨w, hw⟩ := H.rho hM le_rfl hx
  obtain ⟨w', hw'⟩ := H.rho hM le_rfl hy
  rw [H.gam_eq hM le_rfl hxy (H.ex.add _ _ _ _ _ _ _ _ hw hw'), H.gam_eq hM le_rfl hx hw, H.gam_eq hM le_rfl hy hw', map_add (f := _)]
  rfl

theorem lin {r j : ℕ} (c : Y.Λ) {x : Y.Fam M r j} (hx : CB.Comp x) (hc : CB.Comp (c • x)) (a : ℕ) (φ : Module.Dual K (Hdg M.q a j)) :
    gam S (c • x) a φ = Y.θ c * gam S x a φ := by
  obtain ⟨w, hw⟩ := H.rho hM le_rfl hx
  rw [H.gam_eq hM le_rfl hc (H.ex.smul _ _ _ _ c _ _ hw), H.gam_eq hM le_rfl hx hw, ← (S r).θ_lam]
  exact (isCo H.co (S r) hM j r.lt_succ_self).smul _ _ _ _

theorem lin' {r j : ℕ} {x : Y.Fam M r j} (hx : CB.Comp x) (a : ℕ) (k : K) (φ : Module.Dual K (Hdg M.q a j)) :
    gam S x a (k • φ) = kC K k * gam S x a φ := by
  obtain ⟨w, hw⟩ := H.rho hM le_rfl hx
  rw [H.gam_eq hM le_rfl hx hw, ← (S r).θ_K]
  exact (isCo H.co (S r) hM j r.lt_succ_self).lin _ _ _ _

theorem big {r j : ℕ} {x : Y.Fam M r j} (hx : CB.Comp x) (a : ℕ) (ha : r < a) : gam S x a = 0 := by
  obtain ⟨w, hw⟩ := H.rho hM le_rfl hx
  rw [H.gam_eq hM le_rfl hx hw]
  exact (isCo H.co (S r) hM j r.lt_succ_self).big a ha w

set_option maxHeartbeats 1600000 in
theorem sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') {x : Y.Fam M r j} (hx : CB.Comp x) (hs : CB.Comp (CB.shS k h x)) (a : ℕ) :
    gam S (CB.shS k h x) a = gam S x a := by
  have hr : r ≤ r' := by omega
  obtain ⟨w, hw⟩ := H.rho hM hr hx
  rw [H.gam_eq hM le_rfl hs (H.mul.sh _ _ k h _ _ hw), H.gam_eq hM hr hx hw]
  refine AddMonoidHom.ext fun φ => ?_
  have := (aCo H.co (S r') hM j (Nat.lt_succ_of_le hr)).hom (aCo H.co (S r') hM j r'.lt_succ_self) hr (sB := RingHom.id _)
    (RingHom.id _) (fun _ => rfl) (fun _ => rfl) (shG ((S r').QB M) (S r').tB_mem k h j) (fun _ => LinearMap.id) (fun _ => 1)
    (fun a ha y => (H.mul.sh_μ _ _ k h a ha y).trans (one_smul _ _).symm) w a φ
  rw [map_one, one_mul] at this
  exact this

theorem hom' {N : Model l K} (hN : N.Sm) {sΛ : Y.Λ →+* Y.Λ} {sn : ∀ n, Y.R n →+* Y.R n} {sC : ℂ_[l] →+* ℂ_[l]} {c : ℂ_[l]} {r j : ℕ}
    (h : LHom (S r) (S r) sΛ sn sC c) (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p)
    (mm : ∀ n, GlobalTheory.LogCris.Mor (Y.L N n) (Y.L M n) (sn n))
    (hpt : ∀ (n : ℕ) (B₀ : CommRingCat.{0}) (y : (Y.L M n).Pt.obj B₀), ((mm n).pt.app B₀ y).1.2 = (show Spec B₀ ⟶ M.X from y.1.2) ≫ u)
    {x : Y.Fam N r j} (hx : CB.Comp x) (x' : Y.Fam M r j) (hx' : CB.Comp x')
    (hc : ∀ n a, sn n (Y.c n a) = Y.c n (sΛ a)) (e : ∀ n, x' n = (pdOm (mm n) sΛ (hc n) r).pull j (x n))
    (a : ℕ) (φ : Module.Dual K (Hdg M.q a j)) :
    gam S x' a φ = c ^ (r - a) * sC (gam S x a (φ ∘ₗ pullH (Model.genMap u hu) (Model.genMap_q u hu) a j)) := by
  obtain ⟨w, hw⟩ := H.rho hN le_rfl hx
  have h1 := H.hom h u hu mm hpt r j x w hw
  obtain rfl : x' = fun n => (pdOm (mm n) sΛ (h.cris n) r).pull j (x n) := funext e
  rw [H.gam_eq hM le_rfl hx' h1, H.gam_eq hN le_rfl hx hw]
  exact co_hom H.co H.mu h hM hN u hu j r.lt_succ_self w a φ

theorem nat {N : Model l K} (hN : N.Sm) {r j : ℕ} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p)
    {x : Y.Fam N r j} (hx : CB.Comp x) (x' : Y.Fam M r j) (hx' : CB.Comp x')
    (e : ∀ n, x' n = (pdOm (c := Y.c n) (c' := Y.c n) (pullM Y u hu n) (RingHom.id Y.Λ) (fun _ => rfl) r).pull j (x n))
    (a : ℕ) (φ : Module.Dual K (Hdg M.q a j)) :
    gam S x' a φ = gam S x a (φ ∘ₗ pullH (Model.genMap u hu) (Model.genMap_q u hu) a j) := by
  rw [H.hom' hM hN (idH (S r)) u hu (pullM Y u hu) (fun _ _ _ => rfl) hx x' hx' (fun _ _ => rfl) e, one_pow, one_mul]; rfl

theorem gal {sΛ : Y.Λ →+* Y.Λ} {sn : ∀ n, Y.R n →+* Y.R n} {sC : ℂ_[l] →+* ℂ_[l]} {c : ℂ_[l]} {r j : ℕ}
    (h : LHom (S r) (S r) sΛ sn sC c) (mm : ∀ n, GlobalTheory.LogCris.Mor (Y.L M n) (Y.L M n) (sn n))
    (hpt : ∀ (n : ℕ) (B₀ : CommRingCat.{0}) (y : (Y.L M n).Pt.obj B₀), ((mm n).pt.app B₀ y).1.2 = y.1.2)
    {x : Y.Fam M r j} (hx : CB.Comp x) (x' : Y.Fam M r j) (hx' : CB.Comp x')
    (hc : ∀ n a, sn n (Y.c n a) = Y.c n (sΛ a)) (e : ∀ n, x' n = (pdOm (mm n) sΛ (hc n) r).pull j (x n))
    (a : ℕ) (φ : Module.Dual K (Hdg M.q a j)) :
    c ^ a * gam S x' a φ = c ^ r * sC (gam S x a φ) := by
  rcases le_or_gt a r with ha | ha
  · rw [H.hom' hM hM h (𝟙 M.X) (Category.id_comp _) mm (fun n B₀ y => (hpt n B₀ y).trans (Category.comp_id _).symm) hx x' hx' hc e,
      comp_id H.form, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' ha]
  · rw [H.big hM hx a ha, H.big hM hx' a ha]; simp

theorem cup {r r' s i j : ℕ} (h : r + r' = s) {x : Y.Fam M r i} {y : Y.Fam M r' j} (hx : CB.Comp x) (hy : CB.Comp y)
    (hxy : CB.Comp (CB.cupS h x y)) {m m' : ℕ → ℕ} (b : ∀ a, Module.Basis (Fin (m a)) K (Hdg M.q a i))
    (b' : ∀ a, Module.Basis (Fin (m' a)) K (Hdg M.q a j)) (c : ℕ) (φ : Module.Dual K (Hdg M.q c (i + j))) :
    gam S (CB.cupS h x y) c φ = ∑ p : (Finset.HasAntidiagonal.antidiagonal c : Finset (ℕ × ℕ)), ∑ s, ∑ s',
      gam S x p.1.1 ((b p.1.1).coord s) * gam S y p.1.2 ((b' p.1.2).coord s') *
        kC K (φ (cupH M.q (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2) rfl (b p.1.1 s) (b' p.1.2 s'))) := by
  have h1 : r ≤ s := by omega
  have h2 : r' ≤ s := by omega
  obtain ⟨w, hw⟩ := H.rho hM h1 hx
  obtain ⟨w', hw'⟩ := H.rho hM h2 hy
  obtain ⟨β, hβ⟩ := CrystallineSemistableComparison.P.cup_bilin (grOkQ ((S s).QB M) h).pair (rfl : i + j = i + j)
  rw [H.gam_eq hM le_rfl hxy (H.mul.cup _ _ h _ _ _ _ hw hw'), H.gam_eq hM h1 hx hw, H.gam_eq hM h2 hy hw']
  have := (aCo H.co (S s) hM i (Nat.lt_succ_of_le h1)).cup (aCo H.co (S s) hM j (Nat.lt_succ_of_le h2))
    (aCo H.co (S s) hM (i + j) s.lt_succ_self) h (kC K) (S s).θ_K β (fun e y y' => cupH M.q e rfl y y')
    (fun e => H.form.bilin M.q e rfl) (fun e ha ha' y y' => (hβ _ _).trans (H.mul.cup_μ _ _ h e ha ha' y y')) b b' c φ w w'
  rw [hβ] at this
  exact this

theorem one (h1 : CB.Comp (Y.oneS M)) (φ : Module.Dual K (Hdg M.q 0 0)) : gam S (Y.oneS M) 0 φ = kC K (φ (oneH M.q)) := by
  rw [H.gam_eq hM le_rfl h1 (H.mul.one (S 0) M), ← (S 0).θ_K]
  exact (isCo H.co (S 0) hM 0 Nat.one_pos).same 0 le_rfl _ _

theorem c1' (D : E.LineData M.X) (hD : sSup (𝒱D D) = ⊤) (x : Y.Fam M 1 2) (c : Hdg M.q 1 2) (hx : CB.Comp x) (h1 : CB.IsFirstChernClassInFamily D x)
    (h2 : IsDlogFirstChernClass M.q (genD D) c) : (∀ φ, gam S x 1 φ = kC K (φ c)) ∧ ∀ a, a ≠ 1 → gam S x a = 0 := by
  rw [H.gam_eq hM le_rfl hx (H.c1 (S 1) M Nat.one_lt_two D hD x c h1 h2)]
  exact ⟨fun φ => ((isCo H.co (S 1) hM 2 Nat.one_lt_two).same 1 le_rfl _ _).trans ((S 1).θ_K _),
    fun a ha => (isCo H.co (S 1) hM 2 Nat.one_lt_two).diff a 1 ha _⟩

end Hyp

end CrystallineSemistableComparison.HT.H2
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.H1LiftNaturality
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

open PAlg

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem lin_add {R : Type} [CommRing R] {A B C : Type 1} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B]
    [Module R C] (f : A →ₗ[R] C) (g : B →ₗ[R] C) {x x' : A} {y y' y'' : B} (h : f x = g y) (h' : f x' = g y') (e : y'' = y + y') :
    f (x + x') = g y'' := by rw [e, map_add (f := _), map_add (f := _), h, h']

theorem lin_smul {R : Type} [CommRing R] {A B C : Type 1} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B]
    [Module R C] (f : A →ₗ[R] C) (g : B →ₗ[R] C) (c : R) {x : A} {y y' : B} (h : f x = g y) (e : y' = c • y) :
    f (c • x) = g y' := by rw [e, map_smul, map_smul, h]

theorem kill_val (A : PAlg l) (n : ℕ) (x : A.Acr n) : A.cris n ((l : Acris l) ^ n) * x = 0 := by
  rw [map_pow, map_natCast, A.pow_l_acr n, zero_mul]

theorem kill_MH (P : PAlg l ⥤ Type) (n j : ℕ) (x : MH P n j) : ((l : Acris l) ^ n) • x = 0 :=
  GlueE.H_smul_eq_zero _ _ (fun T y => kill_val T.1.obj n y) j x

theorem e_smul (e : E.EtFam l K) (M : Model l K) (j n : ℕ) (z : ℤ_[l]) (v : M.T j) :
    e M n j ((z • v).lev n) = zA l z • e M n j (v.lev n) :=
  ((congrArg (e M n j) (GlobalTheory.EtC.HtL.smul_eq l n n le_rfl M.spc j 0 z (v.1 n))).trans (map_nsmul (e M n j) _ _)).trans
    (GlueE.padic_smul (zA l) n _ (kill_MH M.P n j _) z).symm

theorem zA_chi (σ : K.fixingSubgroup) (r : ℕ) :
    zA l ((DeRhamTwist.Twist.chi0 l σ.1 ^ r : ℤ_[l]ˣ) : ℤ_[l]) = χA (IntermediateField.fixingSubgroupEquiv K σ) ^ r := by
  rw [Units.val_pow_eq_pow_val, map_pow]
  rfl

variable (ht : TFil l) {e : E.EtFam l K} (he : EtP e)
include he

theorem h1_lift_add : ∀ {M : Model l K} {r j : ℕ} {v v' : M.T j} {x x' : Fam M r j},
    IsLift ht e r v x → IsLift ht e r v' x' → IsLift ht e r (v + v') (x + x') :=
  fun {M r j v v' x x'} h h' => ⟨comp_add h.1 h'.1, fun n =>
    lin_add ((βMorF (B.schFn M.p) (okToOC l K) r n).pull j) ((tMor ht ((B.schFn M.p).pt (okToOC l K)) r n).pull j) (h.2 n) (h'.2 n)
      (map_add (e M n j) (v.lev n) (v'.lev n))⟩

theorem h1_lift_smul : ∀ {M : Model l K} {r j : ℕ} {v : M.T j} {x : Fam M r j} (z : ℤ_[l]),
    IsLift ht e r v x → IsLift ht e r (z • v) (zA l z • x) :=
  fun {M r j v x} z h => ⟨comp_smul _ h.1, fun n =>
    lin_smul ((βMorF (B.schFn M.p) (okToOC l K) r n).pull j) ((tMor ht ((B.schFn M.p).pt (okToOC l K)) r n).pull j) (zA l z) (h.2 n)
      (e_smul e M j n z v)⟩

theorem h1_lift_shift : ∀ {M : Model l K} {r r' j : ℕ} {v : M.T j} {x : Fam M r j} (k : ℕ) (h : r + k = r'),
    IsLift ht e r v x → IsLift ht e r' v (shS ht k h x) :=
  fun {M r r' j v x} k h hx => ⟨comp_sh ht k h hx.1, fun n =>
    (β_sh (B.schFn M.p) (okToOC l K) ht k h n j (x n)).trans
      ((congrArg ((shT ht ((B.schFn M.p).pt (okToOC l K)) k h n).pull j) (hx.2 n)).trans (shT_tMor ht _ k h n j _))⟩

theorem h1_lift_galois : ∀ {M : Model l K} {r j : ℕ} {v : M.T j} {x : Fam M r j} (σ : K.fixingSubgroup), IsLift ht e r v x →
    IsLift ht e r (DeRhamTwist.Twist.chi0 l σ.1 ^ r • M.actT j σ v) (galS σ x) :=
  fun {M r j v x} σ hx => ⟨comp_gal σ hx.1, fun n =>
    (β_galF (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K σ) (galOC_okToOC _) r n j (x n)).trans
      ((congrArg ((galT (IntermediateField.fixingSubgroupEquiv K σ) (B.ptTw (B.schFn M.p) (okToOC l K)
          (IntermediateField.fixingSubgroupEquiv K σ) (galOC_okToOC _)) r n).pull j) (hx.2 n)).trans
        ((galT_tMor ht _ _ r n j _).trans
          ((map_smul ((tMor ht ((B.schFn M.p).pt (okToOC l K)) r n).pull j) _ _).symm.trans
            (congrArg ((tMor ht ((B.schFn M.p).pt (okToOC l K)) r n).pull j)
              ((e_smul e M j n ((DeRhamTwist.Twist.chi0 l σ.1 ^ r : ℤ_[l]ˣ) : ℤ_[l]) (M.actT j σ v)).trans
                (congrArg₂ (· • ·) (zA_chi σ r)
                  (he.good.equi M n j (IntermediateField.fixingSubgroupEquiv K σ) (v.lev n)))).symm))))⟩

theorem h1_lift_naturality : ∀ {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) {r j : ℕ} {v : N.T j} {x : Fam N r j},
    IsLift ht e r v x → IsLift ht e r (Model.pullT u hu j v) (pullS u hu x) :=
  fun {M N} u hu {r j v x} hx => ⟨comp_pull u hu hx.1, fun n =>
    (β_pullF (okToOC l K) (B.schMap u hu) r n j (x n)).trans
      ((congrArg ((pullT' ((B.schMap u hu).pt (okToOC l K)) r n).pull j) (hx.2 n)).trans
        ((pullT_tMor ht _ r n j _).trans
          (congrArg ((tMor ht ((B.schFn M.p).pt (okToOC l K)) r n).pull j) (he.good.nat M N u hu n j (v.lev n)).symm)))⟩

end CrystallineSemistableComparison.HT
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.PowZeroSmul
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT

open Pb Mul

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K)

namespace Mul

theorem rS_sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') (n : ℕ) (x : Y.Fam M r j) :
    (L.rS M r' n).pull j (CB.shS k h x n) = (shm (L.QA M) L.t_mem ((l : L.A) ^ n) k h).pull j ((L.rS M r n).pull j (x n)) :=
  redSub_sh M.p m {⊤} (L.d n) (Y.c n) L.lam (L.d_lam n) (Y.ht n) L.t_mem k h j (x n)

theorem rS_cup {r r' s i j : ℕ} (h : r + r' = s) (n : ℕ) (x : Y.Fam M r i) (y : Y.Fam M r' j) :
    (L.rS M s n).pull (i + j) (CB.cupS h x y n) =
      (okm (L.QA M) ((l : L.A) ^ n) h).pair.cup rfl ((L.rS M r n).pull i (x n)) ((L.rS M r' n).pull j (y n)) :=
  redSub_cup M.p m {⊤} (L.d n) (Y.c n) L.lam (L.d_lam n) h (x n) (y n)

theorem rS_one (n : ℕ) : (L.rS M 0 n).pull 0 (Y.oneS M n) = redG' (L.QA M) ((l : L.A) ^ n) 0 0 (oneG (L.QA M)) :=
  redSub_one M.p m {⊤} (L.d n) (Y.c n) L.lam (L.d_lam n)

theorem b_sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') (z : HG (L.QA M) r j) :
    L.bG M r' j (shG (L.QA M) L.t_mem k h j z) = shG (L.QB M) L.tB_mem k h j (L.bG M r j z) :=
  sq_sh ((L.nmB M).smor _ _ (L.nmB_mem M)) (L.lam Y.t ^ k) (L.tB ^ k) (map_pow _ _ _) _ _ _ _ _ _ _ _ j z

theorem b_cup {r r' s i j : ℕ} (h : r + r' = s) (z : HG (L.QA M) r i) (z' : HG (L.QA M) r' j) :
    L.bG M s (i + j) (cupG (L.QA M) h z z') = cupG (L.QB M) h (L.bG M r i z) (L.bG M r' j z') :=
  sq_cup ((L.nmB M).smor _ _ (L.nmB_mem M)) (grOkQ (L.QA M) h) (grOkQ (L.QB M) h) _ _ _ _ _ _ rfl z z'

theorem b_one : L.bG M 0 0 (oneG (L.QA M)) = L.μ M 0 0 0 (oneH M.q) := by
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext (congrArg (Ideal.Quotient.mk _) ?_)))
  change (1 : (s.obj (Fin.last 0)).obj.B) = (s.obj (Fin.last 0)).obj.i (L.tB ^ (0 - 0)) * 1
  rw [Nat.sub_self, pow_zero, map_one, mul_one]

theorem lifts_sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') (x : Y.Fam M r j) (e : ℕ) (z : HG (L.QA M) r j) (hz : L.Lifts e z x) :
    L.Lifts e (shG (L.QA M) L.t_mem k h j z) (CB.shS k h x) := fun n =>
  (red_sh (L.QA M) L.t_mem ((l : L.A) ^ n) k h j z).trans
    ((congrArg ((shm (L.QA M) L.t_mem ((l : L.A) ^ n) k h).pull j) (hz n)).trans
      ((map_smul ((shm (L.QA M) L.t_mem ((l : L.A) ^ n) k h).pull j) _ _).trans
        (congrArg (fun v => (l : L.A) ^ e • v) (rS_sh L M k h n x).symm)))

theorem lifts_cup {r r' s i j : ℕ} (h : r + r' = s) (x : Y.Fam M r i) (y : Y.Fam M r' j) (e e' : ℕ) (z : HG (L.QA M) r i)
    (z' : HG (L.QA M) r' j) (hz : L.Lifts e z x) (hz' : L.Lifts e' z' y) :
    L.Lifts (e + e') (cupG (L.QA M) h z z') (CB.cupS h x y) := fun n =>
  (red_cup (L.QA M) ((l : L.A) ^ n) h z z').trans
    ((congrArg₂ ((okm (L.QA M) ((l : L.A) ^ n) h).pair.cup rfl) (hz n) (hz' n)).trans
      ((cup_smul _ _ _ _ _ _).trans
        (congrArg₂ (fun (a : L.A) (v : HGm (L.QA M) ((l : L.A) ^ n) s (i + j)) => a • v) (pow_add _ _ _).symm
          (rS_cup L M h n x y).symm)))

theorem rho_sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') (x : Y.Fam M r j) (w : HG (L.QB M) r j) (hr : L.Rho x w) :
    L.Rho (CB.shS k h x) (shG (L.QB M) L.tB_mem k h j w) :=
  hr.elim fun e he => he.elim fun z hz => ⟨e, shG (L.QA M) L.t_mem k h j z, lifts_sh L M k h x e z hz.1,
    (map_smul (shG (L.QB M) L.tB_mem k h j) _ _).symm.trans
      ((congrArg (shG (L.QB M) L.tB_mem k h j) hz.2).trans (b_sh L M k h z).symm)⟩

theorem cupG_smul {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) {r r' s i j : ℕ} (h : r + r' = s) (c : b.R) (e e' : ℕ)
    (w : HG Q r i) (w' : HG Q r' j) : c ^ (e + e') • cupG Q h w w' = cupG Q h (c ^ e • w) (c ^ e' • w') := by
  rw [pow_add]
  exact (cup_smul _ _ _ _ _ _).symm

theorem rho_cup {r r' s i j : ℕ} (h : r + r' = s) (x : Y.Fam M r i) (y : Y.Fam M r' j) (w : HG (L.QB M) r i) (w' : HG (L.QB M) r' j)
    (hr : L.Rho x w) (hr' : L.Rho y w') : L.Rho (CB.cupS h x y) (cupG (L.QB M) h w w') :=
  hr.elim fun e he => he.elim fun z hz => hr'.elim fun e' he' => he'.elim fun z' hz' =>
    ⟨e + e', cupG (L.QA M) h z z', lifts_cup L M h x y e e' z z' hz.1 hz'.1,
      (cupG_smul (L.QB M) h (l : L.B) e e' w w').trans ((congrArg₂ (cupG (L.QB M) h) hz.2 hz'.2).trans (b_cup L M h z z').symm)⟩

theorem pow_zero_smul {R : Type} [CommRing R] {V : Type 1} [AddCommGroup V] [Module R V] (c : R) (v : V) : c ^ 0 • v = v := by
  rw [pow_zero, one_smul]

theorem rho_one : L.Rho (Y.oneS M) (L.μ M 0 0 0 (oneH M.q)) :=
  ⟨0, oneG (L.QA M), fun n => (rS_one L M n).symm.trans (pow_zero_smul _ _).symm, (pow_zero_smul _ _).trans (b_one L M).symm⟩

section Rat
variable {K B : Type} [CommRing K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) {X : Scheme.{0}}
  (q : X ⟶ Spec (CommRingCat.of K)) (Q : ObjectProperty (Thick (nlFun γ 0 X q (κA K I)))) {t : B} (ht : t ∈ I)

theorem mu_sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') (a : ℕ) (ha : a ≤ r) (y : Hdg q a j) :
    shG Q ht k h j (muG γ q Q ht a r j y) = muG γ q Q ht a r' j y :=
  sqC_sh (kS γ q Q) (t ^ (r - a)) (t ^ k) (t ^ (r' - a)) (by rw [← pow_add]; congr 1; omega) _ _ _ _ _ _ j y

theorem mu_cup {r r' s i j a a' c : ℕ} (h : r + r' = s) (ha : a + a' = c) (h1 : a ≤ r) (h2 : a' ≤ r') (y : Hdg q a i) (y' : Hdg q a' j) :
    cupG Q h (muG γ q Q ht a r i y) (muG γ q Q ht a' r' j y') = muG γ q Q ht c s (i + j) (cupH q ha rfl y y') :=
  (sqC_cup (kS γ q Q) (grOk (smFun X q) ha) (grOkQ Q h) (t ^ (r - a)) (t ^ (r' - a')) (t ^ (s - c))
    (by rw [← pow_add]; congr 1; omega) _ _ _ _ _ _ rfl y y').symm

end Rat

end Mul

variable (l K) in
theorem mulRho : MulRho l K :=
  ⟨fun {_ _} L M {_ _ _} k h x w hr => rho_sh L M k h x w hr,
   fun {_ _} L M {_ _ _} k h a ha y => mu_sh L.γB M.q (L.QB M) L.tB_mem k h a ha y,
   fun {_ _} L M {_ _ _ _ _} h x y w w' hr hr' => rho_cup L M h x y w w' hr hr',
   fun {_ _} L M {_ _ _ _ _ _ _ _} h ha h1 h2 y y' =>
     mu_cup L.γB M.q (L.QB M) L.tB_mem h ha h1 h2 y y',
   fun {_ _} L M => rho_one L M⟩

end CrystallineSemistableComparison.HT
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.ToYIsFirstChernIff
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

open PAlg Pb

variable {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))


variable (l) in
def CrisSurj : Prop := ∀ n, Function.Surjective ((base l).cris n)

def cb (ht : TFil l) (hs : CrisSurj l) : CB l K where
  Λ := Acris l
  R n := (base l).Acr n
  I n := B.JJ false (base l) n
  γ n := B.DD false (base l) n
  κ n := B.κb (okToOC l K) false n
  c n := (base l).cris n
  c_surj := hs
  t := tA l
  ht := ht (base l)
  θ := θA l
  rd n := (base l).red n.le_succ
  rd_dp n := B.dd_red false _ n.le_succ
  rd_κ n := B.red_κb _ false n.le_succ
  rd_c n := B.red_cris _ n.le_succ

variable {K} (ht : TFil l) (hs : CrisSurj l) {M : Model l K}

def toY {r j : ℕ} (x : Fam M r j) : (cb K ht hs).Fam M r j := x

theorem toY_comp {r j : ℕ} (x : Fam M r j) : CB.Comp (toY ht hs x) ↔ Comp x := Iff.rfl

theorem toY_isFirstChern_iff (D : E.LineData M.X) (x : Fam M 1 2) : CB.IsFirstChernClassInFamily D (toY ht hs x) ↔ IsFirstChernClassInFamily D x := Iff.rfl

variable (l K)

def LvEx : Prop := ∀ (ht : TFil l) (hs : CrisSurj l), Nonempty (LvSys (cb K ht hs) (Γ := K.fixingSubgroup)
  (fun σ => ACris.galCris (IntermediateField.fixingSubgroupEquiv K σ)) (fun σ => galBase (IntermediateField.fixingSubgroupEquiv K σ))
  (fun σ => (period_ring_base.σC σ.1).toRingHom) fun σ => qC l (period_ring_base.χ σ.1))

def Half2Of : Prop := ∀ ht : TFil l, CrisSurj l → LvEx l K → RhoEx l K → CoEx l K → HomRho l K → HomMu l K → MulRho l K →
  FirstChernHodgeTateCompat l K → KForm → KFin → ∃ γ, Half2 (K := K) ht γ

end CrystallineSemistableComparison.HT
end
end

