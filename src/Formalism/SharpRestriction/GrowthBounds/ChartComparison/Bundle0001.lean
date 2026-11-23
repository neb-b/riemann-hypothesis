module

public import Formalism.SharpRestriction.GrowthBounds.ChartComparison.StepIn
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.Bundle0003
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.Bundle0004
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0004
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0010
public import Formalism.LocalToGlobal.HermitianForms.TiedSym
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0077
public import Formalism.LocalRingCardinality.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ChartComparison.IntAtJIffN
section
noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {Tau : Type} [Fintype Tau] {n : ℕ}

theorem val_tw_iff (hn : 0 < n) (k a : ℂ) (hk : k ≠ 0) (ha : a ≠ 0) (G : Tau → Matrix (Fin n) (Fin n) ℂ) (lam : Tau → DomWeight n) (c : ℤ)
    (M : Tau → Matrix (Fin n) (Fin n) ℂ) (hM : ∀ τ, IsUnit (M τ).det) (Q : MvPolynomial (Tau × Fin n × Fin n) ℂ) (z : Formalism.L2.Forms.Frames G) (v : ℂ) :
    v = fnOf G (shiftOf (fun τ => shW (lam τ) c)) M Q z ↔
      k * (a * detF c z * v) = fnOf G (shiftOf lam) M ((k * a * ∏ τ, (M τ).det ^ (-c)) • Q) z := by
  have h1 : fnOf G (shiftOf lam) M ((k * a * ∏ τ, (M τ).det ^ (-c)) • Q) z =
      k * (a * ((∏ τ, (M τ).det ^ (-c)) * fnOf G (shiftOf lam) M Q z)) := by
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h1]
  constructor
  · intro hv
    rw [nrm_val_M hn a G lam c M hM Q z v hv]
  · intro hv
    exact nrm_val_M' hn a ha G lam c M hM Q z v (mul_left_cancel₀ hk hv)

end Gen

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ}
  {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p} (S : StepIn M i hi G)

namespace StepIn

def sTw (β : S.Ch) (cl : {c // S.chOf c = β}) (B' : GL (Fin (D.R.N i)) D.host.E) : ℂ :=
  S.kTw β * ((S.tw β).ch ((S.K β).y cl) : ℂ) *
    ∏ τ, (atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1 τ).det ^ (-(cTw D i))

def TwUnit (w : D.what₂.places.Pl) (β : S.Ch) : Prop :=
  ∀ (cl : {c // S.chOf c = β}) (B' : GL (Fin (D.R.N i)) D.host.E),
    IsLocBasis (D.what₂.places.resChar w) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (S.lat cl.1)) B' →
    ∃ r : D.what₂.LL, r ∈ Formalism.BasicNotions.intW D.what₂.places w ∧ r⁻¹ ∈ Formalism.BasicNotions.intW D.what₂.places w ∧ D.what₂.embLL r = S.sTw β cl B'

def IntAtN (w : D.what₂.places.Pl) (β : S.Ch) (x : (M.lat i).V) (cl : {c // S.chOf c = β}) : Prop :=
  ∀ B' : GL (Fin (D.R.N i)) D.host.E,
    IsLocBasis (D.what₂.places.resChar w) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (S.lat cl.1)) B' →
    ∃ Pp ∈ IntSpan D w (M.lam i), ∀ z : Fr D i hi, S.embN β x cl z =
      fnOf _ (shiftOf (M.lam i)) (atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) Pp z

variable {S}

theorem sTw_ne (β : S.Ch) (cl : {c // S.chOf c = β}) (B' : GL (Fin (D.R.N i)) D.host.E) : S.sTw β cl B' ≠ 0 :=
  mul_ne_zero (mul_ne_zero (S.kTw_ne β) (Units.ne_zero _))
    (Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (atInf_det_unit (embT D) B'⁻¹ τ).ne_zero)


set_option maxHeartbeats 1000000 in
theorem intAtJ_iff_N (w : D.what₂.places.Pl) (β : S.Ch) (hU : S.TwUnit w β) (x : (M.lat i).V) (cl : {c // S.chOf c = β}) :
    S.IntAtJ w β x cl ↔ S.IntAtN w β x cl := by
  refine forall_congr' fun B' => forall_congr' fun hB => ?_
  obtain ⟨r, hr, hr', er⟩ := hU cl B' hB
  have key : ∀ (Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) ℂ) (z : Fr D i hi),
      M.emb i x cl.1 (S.eY.symm z) =
        fnOf _ (shiftOf (lamTG M i)) (atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) Q z ↔
      S.embN β x cl z = fnOf _ (shiftOf (M.lam i)) (atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1)
        (D.what₂.embLL r • Q) z := by
    intro Q z
    rw [er]
    exact val_tw_iff (D.R.N_pos i) (S.kTw β) _ (S.kTw_ne β) (Units.ne_zero _) _ (M.lam i) (cTw D i) _
      (atInf_det_unit (embT D) B'⁻¹) Q z _
  have hr0 : D.what₂.embLL r ≠ 0 := by rw [er]; exact sTw_ne β cl B'
  constructor
  · rintro ⟨Q, hQ, h⟩
    refine ⟨D.what₂.embLL r • Q, intSpan_smul w (M.lam i) r hr hQ, fun z => (key Q z).1 ?_⟩
    rw [h, Equiv.apply_symm_apply]
  · rintro ⟨Q, hQ, h⟩
    refine ⟨D.what₂.embLL r⁻¹ • Q, intSpan_smul w (M.lam i) r⁻¹ hr' hQ, fun z' => ?_⟩
    have h1 := (key (D.what₂.embLL r⁻¹ • Q) (S.eY z')).2 (by
      rw [smul_smul, map_inv₀, mul_inv_cancel₀ hr0, one_smul]
      exact h _)
    rwa [Equiv.symm_apply_apply] at h1

variable (S)

def ValIntN (e : D.what₂.LL →+* G.Kf) (w : D.what₂.places.Pl) : Prop :=
  ∀ β, ValIntAt (S.K β).lev (embT D) D.what₂.embLL (S.charts.gat β) e (S.loc β) S.pos (S.embN β) (S.K β).y (S.IntAtN w β)

variable {S}

theorem valIntJ_of (e : D.what₂.LL →+* G.Kf) (w : D.what₂.places.Pl) (hU : ∀ β, S.TwUnit w β) (h : S.ValIntN e w) : S.ValIntJ e w :=
  fun β x a L cl hL hp => (h β x a L cl hL hp).trans (intAtJ_iff_N w β (hU β) x cl).symm

end StepIn

end Formalism.MainNotions.G.CmpJ

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ChartComparison.LocGoodLocJ
section
noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gramN_apply (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (x y : Fin (D.R.N i)) :
    gramN D i hi x y = (D.sp.X i).gram (Fin.cast (rankN D i hi).symm x) (Fin.cast (rankN D i hi).symm y) := rfl

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {i : ℕ}
  (hi : i + 1 ≤ D.R.m) {cmp : Type} [Fintype cmp] {em : cmp → Lv.compS i}
  {Lb : Submodule (𝓞 D.host.E) (Fin (D.sp.X (i + 1)).rank → D.host.E)}
  {Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))}
  {ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ}
  {eps : UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram →* (D.gat u w hg).Oˣ}
  (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
  (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E)


set_option maxHeartbeats 1000000 in
def locJ : LocAt D.host.F D.host.E (D.R.N (i + 1)) (gatCh (gatJ Lv (i + 1)) em) where
  rk := t.rk.trans (rankN D (i + 1) hi)
  pl := (X.g u w hg).pl
  eQ := fun v => (X.g u w hg).eQ v _ rfl
  spl := fun v => (X.g u w hg).spl _ ((X.g u w hg).pl v).2
  B := reGL (rankN D (i + 1) hi) _ B
  yG := fun c => reGL (rankN D (i + 1) hi) _ (t.yG c).1
  gamI := fun c => (reGL (rankN D (i + 1) hi) D.host.E).toMonoidHom.comp
    ((UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram).subtype.comp (t.gamI c))

def FrRatJ : Prop :=
  ∀ (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
    t.fr w' h =
      bc (((RingHom.fst _ _).comp ((X.g u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B

theorem locJ_UJ (c : cmp) (γ : ((gatCh (gatJ Lv (i + 1)) em).lev c).Γ) :
    (locJ hi t B).gamI c γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi) :=
  reGL_mem_UJ (rankN D (i + 1) hi) _ (D.sp.X (i + 1)).gram _ (gramN_apply D (i + 1) hi) _ (t.gamI c γ).2


set_option maxHeartbeats 4000000 in
theorem locJ_actB (hB : FrRatJ t B) : (locJ hi t B).ActB := by
  refine LocAt.actB_of (locJ hi t B) (rankN D (i + 1) hi) B (fun c γ => (t.gamI c γ).1) rfl (fun _ _ => rfl) ?_
  intro c v γ a b a' b' ha hb
  have h1 := t.act_eq c v _ rfl ((X.g u w hg).pl v).2 γ a b a' b' ha hb
  rw [hB _ ((X.g u w hg).pl v).2, bc_comp] at h1
  exact h1


set_option maxHeartbeats 4000000 in
theorem locGood_locJ : LocGood (sigD D) (gramN D (i + 1) hi) (locJ hi t B) := by
  refine {
    herm := isHerm_re (rankN D (i + 1) hi) _ (D.sp.X (i + 1)).gram _ (gramN_apply D (i + 1) hi) (gram_herm D.sp.cm (D.sp.X (i + 1)))
    det := det_re (rankN D (i + 1) hi) (D.sp.X (i + 1)).gram _ (gramN_apply D (i + 1) hi) (gram_det_unit D.sp.cm (D.sp.X (i + 1)))
    sig := fun v x => (X.g u w hg).spl_sig _ ((X.g u w hg).pl v).2 x
    yG_mem := fun c => reGL_mem_UPts (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram _ (gramN_apply D (i + 1) hi) _ _ (t.yG c).2
    yG_p := ?_ }
  intro c v
  have h1 := t.yG_p c _ ((X.g u w hg).pl v).2
  have h2 := bc_reGL (rankN D (i + 1) hi) (prV (E := D.host.E) ((X.g u w hg).pl v).1) (t.yG c).1
  rw [h1, map_one] at h2
  exact h2

theorem locInt_locJ : LocInt (locJ hi t B) :=
  fun v x => (X.g u w hg).completion_integers_iff v _ rfl x

end Formalism.MainNotions.G.CmpJ

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ChartComparison.OneChartLev
section
noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Idx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau]

theorem FiC_comp (S : StepLevel F E σ J T f bad) (emb : Tau → E →+* ℂ) (lam : Tau → DomWeight n) {c c' : Type}
    (yc : c → UPts σ J (FiniteAdeleRing (𝓞 F) F)) (r : c' → c) (hr : Function.Surjective r)
    (ψ : c → Formalism.L2.Forms.Frames (gramC J emb) → ℂ) :
    (fun a => ψ (r a)) ∈ FiC S emb lam (fun a => yc (r a)) ↔ ψ ∈ FiC S emb lam yc := by
  unfold FiC
  constructor
  · rintro ⟨g, hg, h⟩
    refine ⟨g, hg, ?_⟩
    funext a
    obtain ⟨a', rfl⟩ := hr a
    exact congrFun h a'
  · rintro ⟨g, hg, h⟩
    refine ⟨g, hg, ?_⟩
    funext a
    exact congrFun h (r a)

end Idx

variable {D : D7} {u : D.what₂.Word} {eV : (D.mem u).A.vT ≃ PlT D u} {i : ℕ} {hi : i ≤ D.R.m} {K : ClsTied u i hi}

def IntAtI (V : ValTied u eV i hi K) (w : D.what₂.places.Pl) (x : ((D.fm u).lat i).V) (c : (D.mem u).C.cls i) : Prop :=
  ∀ B : GL (Fin (D.R.N i)) D.host.E,
    IsLocBasis (D.what₂.places.resChar w) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (clsCrd D u i hi c)) B →
    ∃ P ∈ IntSpan D w ((D.fm u).lam i),
      ∀ z, (D.fm u).emb i x c z =
        fnOf _ (shiftOf (lamT u i)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) P (V.eY z)

theorem locW_intAtI (V : ValTied u eV i hi K) (w : D.what₂.places.Pl) (x : ((D.fm u).lat i).V)
    (hx : x ∈ Formalism.BasicNotions.locW D.what₂.places w ((D.fm u).lat i).L) (c : (D.mem u).C.cls i) : IntAtI V w x c := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    intro B hB
    exact (V.lat y).1 hy w c B hB
  | zero =>
    intro B _
    refine ⟨0, AddSubgroup.zero_mem _, fun z => ?_⟩
    rw [map_zero, map_zero]
    rfl
  | add y z _ _ h1 h2 =>
    intro B hB
    obtain ⟨P, hP, hPy⟩ := h1 B hB
    obtain ⟨Q, hQ, hQz⟩ := h2 B hB
    refine ⟨P + Q, AddSubgroup.add_mem _ hP hQ, fun t => ?_⟩
    rw [map_add (f := _), map_add (f := _)]
    show (D.fm u).emb i y c t + (D.fm u).emb i z c t = _
    rw [hPy t, hQz t]
    rfl
  | smul a y _ h1 =>
    intro B hB
    obtain ⟨P, hP, hPy⟩ := h1 B hB
    refine ⟨D.what₂.embLL a.1 • P, intSpan_smul w _ a.1 a.2 hP, fun t => ?_⟩
    rw [Subring.smul_def, LinearMap.map_smulₛₗ, map_smul]
    show D.what₂.embLL a.1 * (D.fm u).emb i y c t = _
    rw [hPy t]
    rfl

theorem exists_denI (u : D.what₂.Word) (i : ℕ) (x : ((D.fm u).lat i).V) :
    ∃ d : 𝓞 D.what₂.LL, d ≠ 0 ∧ d • x ∈ ((D.fm u).lat i).L :=
  _root_.UpperTheory.Reformulated.B.ExistsIdealDenominator.exists_denI u i x

theorem locWBackI (V : ValTied u eV i hi K) (w : D.what₂.places.Pl) (x : ((D.fm u).lat i).V) (hx : ∀ c, IntAtI V w x c) :
    x ∈ Formalism.BasicNotions.locW D.what₂.places w ((D.fm u).lat i).L := by
  have key : ∀ (r : 𝓞 D.what₂.LL) (v : ((D.fm u).lat i).V), r • v = (algebraMap (𝓞 D.what₂.LL) D.what₂.LL r) • v :=
    fun r v => (algebraMap_smul D.what₂.LL r v).symm
  obtain ⟨d, hd0, hdL⟩ := exists_denI u i x
  obtain ⟨s, hsP, hsv⟩ := exists_prime_to_le (D.plEq w) d hd0
  have hs0 : s ≠ 0 := fun h => hsP (h ▸ Submodule.zero_mem _)
  have hsL : s • x ∈ ((D.fm u).lat i).L := by
    refine (V.lat (s • x)).2 ?_
    intro w' c B hB
    by_cases hw : w' = w
    · subst hw
      have hsint : algebraMap (𝓞 D.what₂.LL) D.what₂.LL s ∈ Formalism.BasicNotions.intW D.what₂.places w' := by
        show (0 : WithTop ℤ) ≤ D.what₂.places.val w' _
        rw [Formalism.L2.G.val_nonneg_iff, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact (D.plEq w').intValuation_le_one s
      obtain ⟨P, hP, hPx⟩ := hx c B hB
      refine ⟨D.what₂.embLL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL s) • P, intSpan_smul w' _ _ hsint hP, fun t => ?_⟩
      rw [key, LinearMap.map_smulₛₗ, LinearMap.map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hPx t]
    · have hne : D.plEq w' ≠ D.plEq w := fun h => hw (D.plEq.injective h)
      have hdne : algebraMap (𝓞 D.what₂.LL) D.what₂.LL d ≠ 0 := by
        simpa using hd0
      set q : D.what₂.LL := algebraMap (𝓞 D.what₂.LL) D.what₂.LL s / algebraMap (𝓞 D.what₂.LL) D.what₂.LL d with hq
      have hqint : q ∈ Formalism.BasicNotions.intW D.what₂.places w' := by
        show (0 : WithTop ℤ) ≤ D.what₂.places.val w' _
        rw [Formalism.L2.G.val_nonneg_iff, hq, map_div₀, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        have hdv : (D.plEq w').intValuation d ≠ 0 := (D.plEq w').intValuation_ne_zero d hd0
        rw [div_le_one₀ (zero_lt_iff.2 hdv)]
        exact hsv _ hne
      have hsx : s • x = q • (d • x) := by
        rw [key, key, smul_smul, hq, div_mul_cancel₀ _ hdne]
      obtain ⟨P, hP, hPx⟩ := (V.lat (d • x)).1 hdL w' c B hB
      refine ⟨D.what₂.embLL q • P, intSpan_smul w' _ q hqint hP, fun t => ?_⟩
      rw [hsx, LinearMap.map_smulₛₗ, LinearMap.map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hPx t]
  have hsu : (D.plEq w).intValuation s = 1 := by
    apply le_antisymm ((D.plEq w).intValuation_le_one s)
    by_contra hlt
    exact hsP (((D.plEq w).intValuation_lt_one_iff_mem s).1 (lt_of_not_ge hlt))
  have hsne : algebraMap (𝓞 D.what₂.LL) D.what₂.LL s ≠ 0 := by simpa using hs0
  have htint : (algebraMap (𝓞 D.what₂.LL) D.what₂.LL s)⁻¹ ∈ Formalism.BasicNotions.intW D.what₂.places w := by
    show (0 : WithTop ℤ) ≤ D.what₂.places.val w _
    rw [Formalism.L2.G.val_nonneg_iff, map_inv₀, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hsu, inv_one]
  have hx' : x = (⟨_, htint⟩ : Formalism.BasicNotions.intW D.what₂.places w) • (s • x) := by
    rw [Subring.smul_def, key, smul_smul, inv_mul_cancel₀ hsne, one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hsL)

theorem locWCritI (V : ValTied u eV i hi K) (w : D.what₂.places.Pl) (x : ((D.fm u).lat i).V) :
    x ∈ Formalism.BasicNotions.locW D.what₂.places w ((D.fm u).lat i).L ↔ ∀ c, IntAtI V w x c :=
  ⟨fun hx c => locW_intAtI V w x hx c, locWBackI V w x⟩

def chU (u : D.what₂.Word) (i : ℕ) : (D.mem u).C.cls i → Unit := fun _ => ()

def oneChart (K : ClsTied u i hi) (β : Unit) :
    LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chU u i c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1) where
  lev := K.lev
  y := fun c => K.y c.1
  y_bij := ⟨fun a b h => Subtype.ext (K.y_bij.1 h), fun q => by
    obtain ⟨c, hc⟩ := K.y_bij.2 q
    exact ⟨⟨c, Subsingleton.elim _ _⟩, hc⟩⟩
  y_lat := fun c => K.y_lat c.1
  stabI := fun c => K.stabI c.1
  stabI_inj := fun c => K.stabI_inj c.1
  stabI_range := fun c => K.stabI_range c.1


set_option maxHeartbeats 2000000 in
theorem valTied_toG (V : ValTied u eV i hi K) :
    ValuationCompatibleChart (D.fm u) V.eY (fun _ => True) (chU u i) (lat := clsCrd D u i hi) (oneChart K) := by
  refine ⟨?_, V.rat, fun w _ x => locWCritI V w x⟩
  intro φ
  rw [V.Fi φ]
  constructor
  · intro h β
    exact (FiC_comp K.lev (embT D) (lamT u i) K.y (fun c : {c // chU u i c = β} => c.1)
      (fun c => ⟨⟨c, Subsingleton.elim _ _⟩, rfl⟩) (fun c z => φ c (V.eY.symm z))).2 h
  · intro h
    exact (FiC_comp K.lev (embT D) (lamT u i) K.y (fun c : {c // chU u i c = ()} => c.1)
      (fun c => ⟨⟨c, Subsingleton.elim _ _⟩, rfl⟩) (fun c z => φ c (V.eY.symm z))).1 (h ())

variable {p : ℕ}


variable {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}


end Formalism.MainNotions.G.CmpJ

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ChartComparison.WtTieOf
section
noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G.Cmp

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)

def FillTie (Gt : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : Fills (D.gat u w hg)) : Prop :=
  ∀ (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (b : ℕ) (hb : b < D.R.m),
    ((Fl.w v (b + 1) s : ℤ) : ℚ) = wG D.R ((D.hcW u (Gt.gat_pos u w hg ⟨v, s⟩)).e ⟨b, hb⟩) (b + 1)

theorem rk_of (Gt : GatTies D) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (j : ℕ) : (Fl.Pj (j + 1)).m + 1 = D.R.N (j + 1) := by
  have hk := Gt.gat_k u w hg
  show (D.gat u w hg).P.m + (j + 1) * (Fl.t + 1) + 1 = D.R.k + (j + 1) * (D.R.t + 1)
  rw [ht]
  omega

theorem wtTie_of (Gt : GatTies D) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (hF : FillTie Gt u w hg Fl) (j : ℕ) (hj : j + 1 ≤ D.R.m)
    (rk : (Fl.Pj (j + 1)).m + 1 = D.R.N (j + 1)) :
    WtTie (Fl.Pj (j + 1)) rk (Gt.gat_pos u w hg) (M.lam (j + 1)) := by
  intro (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) i
  have hk := Gt.gat_k u w hg
  show liftWt Fl.t (D.gat u w hg).P.m ((D.gat u w hg).P.lam0 v s) (fun a => Fl.w v a s) (j + 1) i =
    (M.lam (j + 1) (Gt.gat_pos u w hg ⟨v, s⟩)).w (finCongr rk i)
  apply Int.cast_injective (α := ℚ)
  rw [M.lam_eq (j + 1) hj (Gt.gat_pos u w hg ⟨v, s⟩) (finCongr rk i)]
  have hi : ((finCongr rk i : Fin (D.R.N (j + 1))) : ℕ) = i.val := rfl
  unfold liftWt
  by_cases h1 : i.val < (D.gat u w hg).P.m + 1
  · have h2 : ((finCongr rk i : Fin (D.R.N (j + 1))) : ℕ) < D.R.k := by rw [hi, ← hk]; exact h1
    rw [dif_pos h1, dif_pos h2, Gt.gat_lam u w hg v s ⟨i.val, h1⟩, (D.fm u).lam_eq 0 (Nat.zero_le _) _ _]
    exact dif_pos h2
  · have h2 : ¬ ((finCongr rk i : Fin (D.R.N (j + 1))) : ℕ) < D.R.k := by rw [hi, ← hk]; exact h1
    rw [dite_eq_right h1, dite_eq_right h2, Int.cast_neg]
    congr 1
    have e1 : (i.val - ((D.gat u w hg).P.m + 1)) / (Fl.t + 1) =
        (((finCongr rk i : Fin (D.R.N (j + 1))) : ℕ) - D.R.k) / (D.R.t + 1) := by rw [hk, ht, hi]
    rw [e1]
    exact hF v s _ (D.R.blk_lt hj (finCongr rk i) h2)


variable {M} in
theorem StepIn.wt_of (Gt : GatTies D) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    {Fl : Fills (D.gat u w hg)} (Lv : Levels Fl) (ht : Fl.t = D.R.t) (hF : FillTie Gt u w hg Fl) (j : ℕ) (hj : j + 1 ≤ D.R.m)
    (S : StepIn M (j + 1) hj (gatJ Lv (j + 1))) (hpos : S.pos = Gt.gat_pos u w hg) (β : S.Ch) :
    WtTie (gatJ Lv (j + 1)).P (S.loc β).rk S.pos (M.lam (j + 1)) := by
  rw [hpos]
  exact wtTie_of M Gt w hg Fl ht hF j hj _

end Formalism.MainNotions.G.CmpJ

end
end

