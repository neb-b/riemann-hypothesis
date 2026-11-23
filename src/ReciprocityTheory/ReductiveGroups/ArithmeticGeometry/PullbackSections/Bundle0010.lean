module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RegTie
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

section Comparison₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]

def SecTieK {t : SAB H (Sp V)} {tK : SAB H (Sp (FractionRing V))} (m : SABMap tK t (Out.jK V))
    (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)) (k : ℕ)
    (F : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V))))))
    (σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ)))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ tK.G.left) (zp : Z ⟶ (𝟙_ (Over (Sp (FractionRing V))) ⊗ tK.G).left),
    zp ≫ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left = r →
    ∀ (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) (J' : (Z ⟶ tK.G.left) → tK.PP.L.ι),
      Good t.PP.L z J → Good tK.PP.L z J' →
      sval σ (r ≫ m.φ) z J = ((gv w r z (fun _ => J (r ≫ m.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval F zp z J'

end Comparison₂

def RegUnifSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ θ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((1 : ℕ) : ℤ))),
      (∀ σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((1 : ℕ) : ℤ))),
        ∃! a : V, ∀ i, σ.f i = resG t.G.left le_top ((t.G.hom).appTop.hom (toΓ V a)) * θ.f i) →
    ∀ (M : ℕ), IsUnit (M : V) →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (θK : LB.Sec (LPow tK.G tK.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))), SecTieK m w 1 θK θ →
    ∀ (t₀ : 𝟙_ (Over (Sp (FractionRing V))) ⟶ tK.G)
      (F : LB.Sec (LPow tK.G tK.PP.L ((M : ℤ) ^ 2) (𝟙_ (Over (Sp (FractionRing V)))))),
      IsVtOver tK.G tK.PP M (fun u => u ^ (M ^ 2) = 1) (zCast tK.G (Nat.cast_one) θK) t₀ F →
      ∃ σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((M ^ 2 : ℕ) : ℤ))),
        SecTieK m w (M ^ 2) (zCast tK.G (natCast_sq M) F) σ

section Move

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def TieMv {X₀ : Scheme.{0}} {t₀ : SAB H X₀} {K : Type} [Field K] {x : Sp K ⟶ X₀} {tK : SAB H (Sp K)}
    (m1 : SABMap tK t₀ x) (w1 : LB.Iso tK.PP.L (t₀.PP.L.pull m1.φ)) (k : ℕ)
    (F : LB.Sec (LPow t₀.G t₀.PP.L (k : ℤ) (Over.mk x)))
    (FK : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp K))))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ tK.G.left) (zp : Z ⟶ (Over.mk x ⊗ t₀.G).left)
    (zp' : Z ⟶ (𝟙_ (Over (Sp K)) ⊗ tK.G).left),
    zp ≫ (snd (Over.mk x) t₀.G).left = r ≫ m1.φ → zp ≫ (fst (Over.mk x) t₀.G).left = r ≫ tK.G.hom →
    zp' ≫ (snd (𝟙_ (Over (Sp K))) tK.G).left = r →
    ∀ (z : Z) (J : (Z ⟶ t₀.G.left) → t₀.PP.L.ι) (J' : (Z ⟶ tK.G.left) → tK.PP.L.ι),
      Good t₀.PP.L z J → Good tK.PP.L z J' →
      sval F zp z J = ((gv w1 r z (fun _ => J (r ≫ m1.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval FK zp' z J'

end Move

def VtMoveSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X₀ : Scheme.{0}) (t₀ : SAB H X₀)
    (K : Type) [Field K] (x : Sp K ⟶ X₀) (tK : SAB H (Sp K)) (m1 : SABMap tK t₀ x)
    (w1 : LB.Iso tK.PP.L (t₀.PP.L.pull m1.φ)), RigIso m1 w1 →
    ∀ (N : ℕ) (ok : (Over.mk x ⟶ t₀.G) → Prop) (s : LB.Sec (LPow t₀.G t₀.PP.L 1 (Over.mk x)))
      (tt : Over.mk x ⟶ t₀.G) (F : LB.Sec (LPow t₀.G t₀.PP.L ((N : ℤ) ^ 2) (Over.mk x))),
      IsVtOver t₀.G t₀.PP N ok s tt F → (∀ u, ok u → u ^ (N ^ 2) = 1) →
    ∀ sK : LB.Sec (LPow tK.G tK.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp K)))),
      TieMv m1 w1 1 (zCast t₀.G Nat.cast_one.symm s) sK →
      ∃ (ttK : 𝟙_ (Over (Sp K)) ⟶ tK.G) (FK : LB.Sec (LPow tK.G tK.PP.L ((N : ℤ) ^ 2) (𝟙_ (Over (Sp K))))),
        IsVtOver tK.G tK.PP N (fun u => u ^ (N ^ 2) = 1) (zCast tK.G Nat.cast_one sK) ttK FK ∧
        TieMv m1 w1 (N ^ 2) (zCast t₀.G (natCast_sq N) F) (zCast tK.G (natCast_sq N) FK)

def ThetaTieSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (Tc : CDVR) (io : c.F →+* Tc.Fr) (y : letI := io.toAlgebra; FrPt Xo c Tc.Fr)
    (I : IntData Xo c Tc io y),
    letI := io.toAlgebra
    ∃ θ : LB.Sec (LB.LinComb I.G.PP.L (K := Fin 1) (fun _ => 𝟙 I.G.G.left) (fun _ => ((1 : ℕ) : ℤ))),
      (∀ σ : LB.Sec (LB.LinComb I.G.PP.L (K := Fin 1) (fun _ => 𝟙 I.G.G.left) (fun _ => ((1 : ℕ) : ℤ))),
        ∃! a : Tc.V, ∀ i, σ.f i = resG I.G.G.left le_top ((I.G.G.hom).appTop.hom (toΓ Tc.V a)) * θ.f i) ∧
      ∃ θK : LB.Sec (LPow I.t'.G I.t'.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp Tc.Fr)))),
        TieMv I.m1 I.w1 1 (zCast Xo.univ.t.G Nat.cast_one.symm y.s) θK ∧ SecTieK I.m2 I.w2 1 θK θ

section Restrict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}

def gsec (G : Over S) : G.left ⟶ (𝟙_ (Over S) ⊗ G).left := (lift (toUnit G) (𝟙 G)).left

theorem gsec_snd (G : Over S) : gsec G ≫ (snd (𝟙_ (Over S)) G).left = 𝟙 _ := by
  rw [gsec, ← Over.comp_left, lift_snd, Over.id_left]

theorem exists_restrict (t : SAB H S) (a : ℤ) (F : LB.Sec (LPow t.G t.PP.L a (𝟙_ (Over S)))) :
    ∃ σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => a)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
        sval σ r z J = sval F (r ≫ gsec t.G) z J := by
  have hF : FormEq (Sum.elim (fun k => gsec t.G ≫ (fun _ : Fin 1 => (snd (𝟙_ (Over S)) t.G).left) k)
      (PEmpty.elim : PEmpty → _)) (Sum.elim (fun _ : Fin 1 => a) (PEmpty.elim : PEmpty → ℤ))
      (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => a) := by
    intro U _ h
    have e := gsec_snd t.G
    simp only [Fintype.prod_sum_type, Sum.elim_inl, e, Finset.univ_eq_empty, Finset.prod_empty, _root_.mul_one]
  obtain ⟨σ, hσ⟩ := exists_sec t.PP.isLB hF
    (pullMulSec (F : LB.Sec (LB.LinComb t.PP.L (fun _ : Fin 1 => (snd (𝟙_ (Over S)) t.G).left) (fun _ => a)))
      (gsec t.G) (LB.oneGen t.PP.L) (fun _ _ => by dsimp only [LB.oneGen]; erw [map_one, map_one, _root_.mul_one]; simp [LB.LinComb]; rfl))
  refine ⟨σ, fun Z r z J hJ => ?_⟩
  refine (hσ Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ r z hJ).trans ?_)
  rw [val_one, Units.val_one, _root_.mul_one]

end Restrict

theorem isUnit_natCast_of_overLa {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} (Tc : CDVR)
    {io : K →+* Tc.Fr} {e : ℕ} (ho : OverLa la Tc.V io e) {M : ℕ} (hM : (M : 𝓞 K) ∉ la.asIdeal) :
    IsUnit (M : Tc.V) := by
  have h1 : la.valuation K (M : K) = 1 := by
    have e1 : (M : K) = algebraMap (𝓞 K) K (M : 𝓞 K) := by simp
    rw [e1, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hM
  have h2 := ho.2 (M : K)
  rw [vLa, h1, WithZero.log_one, neg_zero, mul_zero, map_natCast] at h2
  have e2 : ((M : ℕ) : Tc.Fr) = algebraMap Tc.V Tc.Fr (M : Tc.V) := by simp
  rw [e2, vV, valV, HeightOneSpectrum.valuation_of_algebraMap, neg_eq_zero] at h2
  have hne : (IsDiscreteValuationRing.maximalIdeal Tc.V).intValuation (M : Tc.V) ≠ 0 := by
    refine HeightOneSpectrum.intValuation_ne_zero _ _ ?_
    intro h0
    apply hM
    have : M = 0 := by exact_mod_cast h0
    rw [this, Nat.cast_zero]; exact la.asIdeal.zero_mem
  have h3 : (IsDiscreteValuationRing.maximalIdeal Tc.V).intValuation (M : Tc.V) = 1 := by
    rw [← WithZero.exp_log hne, h2, WithZero.exp_zero]
  rw [HeightOneSpectrum.intValuation_eq_one_iff] at h3
  by_contra hu
  exact h3 ((IsLocalRing.mem_maximalIdeal _).2 hu)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ShortPlaceB
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

def AdaptAt {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : GenLat E n) {K : Type} [Field K] [NumberField K]
    (la : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∃ k : ℕ, ((k : 𝓞 K) ∉ la.asIdeal) ∧ Ideal.span {(k : 𝓞 E)} • Λ.La ≤ stdLat E n ∧
    Ideal.span {(k : 𝓞 E)} • stdLat E n ≤ Λ.La

section Ultra

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem le_nval_sum (e : ℕ) {ι : Type} (s : Finset ι) (f : ι → K') (r : EReal) (h : ∀ i ∈ s, r ≤ nval V e (f i)) :
    r ≤ nval V e (∑ i ∈ s, f i) := by
  classical
  unfold nval at h ⊢
  split_ifs with hs
  · exact le_top
  · have hne : s.Nonempty := by
      by_contra hn
      rw [Finset.not_nonempty_iff_eq_empty] at hn
      exact hs (by rw [hn, Finset.sum_empty])
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image s (fun i => valV V (f i)) hne
    have hle : valV V (∑ i ∈ s, f i) ≤ valV V (f i) := Valuation.map_sum_le _ hmax
    have hfi : f i ≠ 0 := by
      intro h0
      rw [h0, Valuation.map_zero] at hle
      exact hs ((Valuation.zero_iff _).1 (le_antisymm hle zero_le'))
    have h1 := h i hi
    rw [if_neg hfi] at h1
    refine h1.trans ?_
    have hlog := (WithZero.log_le_log ((Valuation.ne_zero_iff _).2 hs) ((Valuation.ne_zero_iff _).2 hfi)).2 hle
    refine EReal.coe_le_coe_iff.2 ?_
    have hl : ((-(valV V (f i)).log : ℤ) : ℝ) ≤ ((-(valV V (∑ i ∈ s, f i)).log : ℤ) : ℝ) := by
      exact_mod_cast neg_le_neg hlog
    exact div_le_div_of_nonneg_right hl (Nat.cast_nonneg e)

end Ultra

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanInst
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

theorem indepToC_comp {K : Type*} [Field K] {σ : K →+* ℂ} {C C' : Type*} [AddCommGroup C] [Module K C]
    [AddCommGroup C'] [Module K C'] {W : Type*} [AddCommGroup W] [Module ℂ W] (J : C →ₛₗ[σ] W)
    (hJ : IndepToC J) (ι : C' →ₗ[K] C) (hι : Function.Injective ι) : IndepToC (J.comp ι) := by
  intro n b hb
  exact hJ n (fun i => ι (b i)) (hb.map' ι (LinearMap.ker_eq_bot.mpr hι))

variable {D : D7} {T : Top D}

set_option synthInstance.maxHeartbeats 400000 in
def jRec (j : ℕ) (ka : WeightFamilies.Wt D j) :
    cutR T.C j ka →ₛₗ[T.σ₀] FDSec (T.U j T.σ₀).X :=
  (rdC (T.U j) T.σ₀ (wtA ka) ka.n).comp (Submodule.inclusion (cutR_le T.C j ka))

set_option synthInstance.maxHeartbeats 400000 in
theorem spanAt_rec (h : LawsP T) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka : WeightFamilies.Wt D j)
    (hJ : JInjRd T j (wtA ka) ka.n) (A : Set (FDSec (T.U j T.σ₀).X))
    (hG : holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA ka) ka.n) ≤ Submodule.span ℂ A)
    (hA : A ⊆ Submodule.span ℂ (jRec (T := T) j ka ''
      (((recX h) j h1 h2).shortTh ka : Set ((recB h.toLawsCore).Cusp j ka)))) :
    SpanAt ((recX h) j h1 h2) ka :=
  spanAt_of_chain ((recX h) j h1 h2) ka (jRec (T := T) j ka)
    (indepToC_comp _ hJ _ (Submodule.inclusion_injective _))
    (holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA ka) ka.n)) A
    (fun _ => rdC_mem_holSub0 T.good_σ₀ (wtA ka) ka.n _) hG hA

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SubMulPf
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem lieFacAdd : LieFacAddSt := by
  intro E _ _ _ H Dw x a a'
  simp only [Formalism.L2.Pj.lieFac, ← Real.exp_add]
  congr 1
  simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]
  ring

theorem pnormMul : PnormMulSt := by
  intro E _ _ _ r X la la' P Q x hx
  have hne : ∀ τ j, ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ j ≠ 0 := fun τ j h => by
    have h1 := (hx τ).2 j
    rw [h, Complex.zero_re, mul_zero] at h1
    exact lt_irrefl 0 h1
  have hpos : ∀ τ (i : Fin r), 0 < ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ /
      ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ := fun τ i =>
    norm_pos_iff.2 (div_ne_zero (hne τ _) (hne τ _))
  have key : ∀ τ (i : Fin r), ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ /
      ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^ (-((la + la') τ i : ℝ) / 2) =
      ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^
          (-(la τ i : ℝ) / 2) *
        ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^
          (-(la' τ i : ℝ) / 2) := fun τ i => by
    rw [← Real.rpow_add (hpos τ i)]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    ring
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
  rw [Pi.mul_apply, norm_mul]
  simp only [key, Finset.prod_mul_distrib]
  ring

theorem pnorm_nonneg' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : 0 ≤ X.pnorm la P x :=
  mul_nonneg (norm_nonneg _) (Formalism.L2.Pj.pnorm_fac_nonneg X la x)

theorem supCMul : SupCMulSt := by
  intro E _ _ _ H Dw l Xo c r U x σ a a' n n' f g _ hn hn' hf hg
  unfold supC
  rw [lieFacAdd E H Dw x a a', rdU_mul]
  have hla : laU (U σ) (a + a') (n + n') = laU (U σ) a n + laU (U σ) a' n' :=
    funext fun k => laU_add (U σ) a a' n n' hn hn' k
  rw [hla]
  have hE : Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n + laU (U σ) a' n') (rdU (U σ) f * rdU (U σ) g) ≤
      Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) *
        Formalism.L2.Pj.supE (U σ).X (laU (U σ) a' n') (rdU (U σ) g) := by
    unfold Formalism.L2.Pj.supE
    refine iSup_le fun p => ?_
    have e := pnormMul E r ((U σ).X p.1) (laU (U σ) a n p.1) (laU (U σ) a' n' p.1) (rdU (U σ) f p.1)
      (rdU (U σ) g p.1) p.2.1 p.2.2
    refine le_trans (le_of_eq ?_) (mul_le_mul' (le_iSup (fun q : FPt (U σ).X =>
      ENNReal.ofReal (((U σ).X q.1).pnorm (laU (U σ) a n q.1) (rdU (U σ) f q.1) q.2)) p)
      (le_iSup (fun q : FPt (U σ).X =>
      ENNReal.ofReal (((U σ).X q.1).pnorm (laU (U σ) a' n' q.1) (rdU (U σ) g q.1) q.2)) p))
    rw [← ENNReal.ofReal_mul (pnorm_nonneg' _ _ _ _)]
    exact congrArg ENNReal.ofReal e
  have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top hf hg) hE
  rw [ENNReal.toReal_mul] at h1
  unfold Formalism.L2.Pj.supN
  calc lieFac Dw x a * lieFac Dw x a' *
        (Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n + laU (U σ) a' n') (rdU (U σ) f * rdU (U σ) g)).toReal
      ≤ lieFac Dw x a * lieFac Dw x a' * ((Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n) (rdU (U σ) f)).toReal *
          (Formalism.L2.Pj.supE (U σ).X (laU (U σ) a' n') (rdU (U σ) g)).toReal) :=
        mul_le_mul_of_nonneg_left h1 (mul_pos (lieFac_pos _ _ _) (lieFac_pos _ _ _)).le
    _ = _ := by ring

theorem recSubMul : RecSubMulSt := by
  intro D T h j hj σ w w' F G H hH
  have hFm : (F : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n := cutR_le T.C j w F.2
  have hGm : (G : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w') w'.n := cutR_le T.C j w' G.2
  have hprod : (H : T.R j) = (F : T.R j) * (G : T.R j) := by
    have h1 := congrArg (fun x : AddMonoidAlgebra (T.R j) (Deg D j) => x.coeff (deg (Formalism.MainNotions.WeightAlgebra.wadd w w'))) hH
    change (incG deg (cutR T.C j) (Formalism.MainNotions.WeightAlgebra.wadd w w') H).coeff _ =
      (incG deg (cutR T.C j) w F * incG deg (cutR T.C j) w' G).coeff _ at h1
    rw [incG_apply, incG_apply, incG_apply, AddMonoidAlgebra.single_mul_single, ← deg_wadd] at h1
    simpa [AddMonoidAlgebra.coeff_single] using h1
  show cutN T.C T.Ns j (Formalism.MainNotions.WeightAlgebra.wadd w w') σ H ≤ cutN T.C T.Ns j w σ F * cutN T.C T.Ns j w' σ G
  unfold cutN
  rw [if_pos hj, if_pos hj, if_pos hj]
  unfold Core.Ns
  rw [hprod, wtA_wadd]
  exact supCMul _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (goodEmb_goodOf _ σ) w.n_even w'.n_even
    (supE_cusp_ne_top (goodEmb_goodOf _ σ) hFm) (supE_cusp_ne_top (goodEmb_goodOf _ σ) hGm)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

