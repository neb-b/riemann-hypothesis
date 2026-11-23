module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0210
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0211
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0189
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0206
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0209
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0143
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormEqRadialFormOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0090
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0096

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FltZeroEq
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem colN {ζ : B.Mat k r} (hζ : B.inLie k r ζ) (z : Fin (2 * r + k + 1) → ℂ)
    (hN : ∀ X ∈ lieOf (Sset k r z), (Matrix.trace (ζ * X)).re = 0) (a : Fin r) :
    ∀ i : Fin (2 * r + k + 1), a.val < i.val → (ζ *ᵥ bvec (eI k r a)) i = 0 := by
  have orth : ∀ v : Fin (2 * r + k + 1) → ℂ, (∀ b : Fin r, b.val ≤ a.val → v (esI k r b) = 0) →
      herm (Hpk k r) (ζ *ᵥ bvec (eI k r a)) v = 0 := by
    intro v hv
    refine herm_zero_of_trace hζ _ v (hN _ (xuv_lieN z a v hv)) (hN _ (xuv_lieN z a _ ?_))
    intro b hb; simp [hv b hb]
  intro i hi
  by_cases h1 : i.val < r
  · have e := herm_es (ζ *ᵥ bvec (eI k r a)) ⟨i.val, h1⟩
    rw [show eI k r ⟨i.val, h1⟩ = i from Fin.ext rfl] at e
    rw [← e]
    refine orth _ (fun b hb => ?_)
    have : esI k r b ≠ esI k r ⟨i.val, h1⟩ := by
      intro h; have := congrArg Fin.val h; simp [esI] at this; omega
    simp [bvec, this]
  · by_cases h2 : i.val ≤ r + k
    · have hw := herm_w (ζ *ᵥ bvec (eI k r a)) i (by omega) h2
      have h0 : herm (Hpk k r) (ζ *ᵥ bvec (eI k r a)) (bvec i) = 0 := by
        refine orth _ (fun b hb => ?_)
        have : esI k r b ≠ i := by
          intro h; have := congrArg Fin.val h; simp [esI] at this; omega
        simp [bvec, this]
      rw [hw] at h0
      split_ifs at h0 with h3
      · exact neg_eq_zero.1 h0
      · exact h0
    · have e : i = esI k r ⟨2 * r + k - i.val, by omega⟩ := by
        apply Fin.ext; simp [esI]; omega
      have e2 := herm_e (ζ *ᵥ bvec (eI k r a)) ⟨2 * r + k - i.val, by omega⟩
      rw [← e] at e2
      rw [← e2]
      refine orth _ (fun b hb => ?_)
      have : esI k r b ≠ eI k r ⟨2 * r + k - i.val, by omega⟩ := by
        intro h; have := congrArg Fin.val h; simp [esI, eI] at this; omega
      simp [bvec, this]

theorem flt_bvec (a : ℕ) (c : Fin r) (hc : c.val < a) : Flt (k := k) a (bvec (eI k r c)) := by
  intro i hi
  have : i ≠ eI k r c := by intro h; rw [h] at hi; simp [eI] at hi; omega
  simp [bvec, this]

theorem flt_zero_eq (y : Fin (2 * r + k + 1) → ℂ) (hy : Flt 0 y) : y = 0 := by
  funext i; exact hy i (Nat.zero_le _)

theorem stepNil (ζ : B.Mat k r) (N : ℕ) (hζN : ζ ^ N = 0) (a : Fin r)
    (hcol : ∀ i : Fin (2 * r + k + 1), a.val < i.val → (ζ *ᵥ bvec (eI k r a)) i = 0)
    (hkill : ∀ y, Flt a.val y → ζ *ᵥ y = 0) : Flt a.val (ζ *ᵥ bvec (eI k r a)) := by
  set ea := bvec (eI k r a) with hea
  set x := ζ *ᵥ ea with hx
  set xa := x (eI k r a)
  have hea1 : ea (eI k r a) = 1 := by simp [hea, bvec]
  have hy : Flt a.val (x - xa • ea) := by
    intro i hi
    by_cases he : i = eI k r a
    · rw [he]; simp only [Pi.sub_apply, Pi.smul_apply, hea1, smul_eq_mul, mul_one]; exact sub_self _
    · have hi' : a.val < i.val := by
        have : i.val ≠ a.val := fun h => he (Fin.ext h)
        omega
      simp [hcol i hi', hea, bvec, he]
  have hζx : ζ *ᵥ x = xa • x := by
    have e : x = xa • ea + (x - xa • ea) := by abel
    conv_lhs => rw [e]
    rw [mulVec_add, mulVec_smul, hkill _ hy, add_zero]
  have hp : ∀ m, (ζ ^ (m + 1)) *ᵥ ea = xa ^ m • x := by
    intro m
    induction m with
    | zero => simp [hx]
    | succ m ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hζx, smul_smul, pow_succ]
  have hxa : xa = 0 := by
    cases N with
    | zero =>
      exfalso
      have := congrFun (congrArg (fun M => M *ᵥ ea) hζN) (eI k r a)
      simp [hea1] at this
    | succ m =>
      have := congrFun (hp m) (eI k r a)
      rw [hζN, zero_mulVec] at this
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this
      have h2 : xa ^ (m + 1) = 0 := by rw [pow_succ]; exact this.symm
      exact (pow_eq_zero_iff'.1 h2).1
  have : x = x - xa • ea := by rw [hxa, zero_smul, sub_zero]
  rw [this]; exact hy

theorem killX (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r)
    (hD : ∀ a (ha : a ≤ r), Dmin k r z z' g ⟨a, by omega⟩ ≠ 0)
    (ξ η : B.Mat k r) (hξ : B.inLie k r ξ) (N : ℕ) (hξN : ξ ^ N = 0) (hηN : η ^ N = 0)
    (hgη : g * η = ξ * g)
    (colξ : ∀ a : Fin r, ∀ i : Fin (2 * r + k + 1), a.val < i.val → (ξ *ᵥ bvec (eI k r a)) i = 0)
    (colη : ∀ a : Fin r, ∀ i : Fin (2 * r + k + 1), a.val < i.val → (η *ᵥ bvec (eI k r a)) i = 0) :
    ∀ a, a ≤ r → ∀ y, Flt a y → ξ *ᵥ y = 0 ∧ η *ᵥ y = 0 := by
  have hξg : ∀ y, ξ *ᵥ (g *ᵥ y) = g *ᵥ (η *ᵥ y) := by
    intro y; rw [mulVec_mulVec, mulVec_mulVec, hgη]
  intro a
  induction a with
  | zero =>
    intro _ y hy
    rw [flt_zero_eq y hy, mulVec_zero, mulVec_zero]
    exact ⟨rfl, rfl⟩
  | succ a ih =>
    intro ha y hy
    have IH := ih (by omega)
    set a' : Fin r := ⟨a, by omega⟩
    have hxξ : Flt a (ξ *ᵥ bvec (eI k r a')) := stepNil ξ N hξN a' (colξ a') (fun y hy => (IH y hy).1)
    have hxη : Flt a (η *ᵥ bvec (eI k r a')) := stepNil η N hηN a' (colη a') (fun y hy => (IH y hy).2)
    have hξa : ξ *ᵥ bvec (eI k r a') = 0 := by
      refine dlem_ii z z' g a (by omega) (hD a (by omega)) _ hxξ (fun c hc => ?_)
      rw [herm_skew hξ, hξg, (IH _ (flt_bvec a c hc)).2, mulVec_zero, herm_zero_right, neg_zero]
    have hηa : η *ᵥ bvec (eI k r a') = 0 := by
      refine dlem_i z z' g a (by omega) (hD a (by omega)) _ hxη (fun c hc => ?_)
      rw [← hξg, herm_skew hξ, (IH _ (flt_bvec a c hc)).1, herm_zero_right, neg_zero]
    set ya := y (eI k r a')
    have hrest : Flt a (y - ya • bvec (eI k r a')) := by
      intro i hi
      by_cases he : i = eI k r a'
      · rw [he]; simp [bvec, ya]
      · have hi' : a + 1 ≤ i.val := by
          have : i.val ≠ a := fun h => he (Fin.ext h)
          omega
        simp [hy i hi', bvec, he]
    have e : y = ya • bvec (eI k r a') + (y - ya • bvec (eI k r a')) := by abel
    rw [e, mulVec_add, mulVec_smul, mulVec_add, mulVec_smul, hξa, hηa, (IH _ hrest).1, (IH _ hrest).2]
    simp

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameTransportToLastLevel
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.WordCorrespondence

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

theorem transport_gen {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (k n i r' : ℕ) (hn : i + r' = n) (hr' : r' = 0)
    {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * r' + k + 1) → ℂ}
    (hz : D.castV hn (liftVec k i r' zs) = z) (hz' : D.castV hn (liftVec k i r' zs') = z')
    {π : Mx k n → (Wp →L[ℂ] Wp)} {π' : Mx k n → (Wq →L[ℂ] Wq)} {πs : Mx k r' → (Wp →L[ℂ] Wp)}
    {πs' : Mx k r' → (Wq →L[ℂ] Wq)}
    (hπ : ∀ y, πs y = π (D.castM hn (ιLev k i r' y))) (hπ' : ∀ y, πs' y = π' (D.castM hn (ιLev k i r' y)))
    (X₀ : ActualOps k n z z' π π') (L₀ : R.LevelData (Pr (RadSp k n z z' π π')) n)
    (st₀ : Fr.Start (Pr (RadSp k n z z' π π')))
    (X : ActualOps k r' zs zs' πs πs') (L : R.LevelData (Pr (RadSp k r' zs zs' πs πs')) r')
    (st : Fr.Start (Pr (RadSp k r' zs zs' πs πs')))
    (hL₀ : IsActualLevel X₀ L₀) (hL : IsActualLevel X L) (s : ℂ) (hst₀ : ∀ Y, st₀.QQ Y = s • X₀.QQ Y)
    (hst : ∀ Y, st.QQ Y = s • X.QQ Y) (hq : st₀.q = st.q) (hinv : st₀.inv = st.inv)
    (hSL₀ : Fr.IsStarLevel L₀) (hSL : Fr.IsStarLevel L) (hs₀ : Fr.IsLevelStart L₀ st₀) (hs : Fr.IsLevelStart L st)
    (c : Fin n → ℂ) (hc : c ∈ OmX n) :
    ∃ T : RadSp k n z z' π π' →ₗ[ℂ] RadSp k r' zs zs' πs πs',
      (∀ Ψ c' g, (T Ψ : Fn k r' (Wq →L[ℂ] Wp)) c' g = (Ψ : Fn k n (Wq →L[ℂ] Wp)) c (D.castM hn (ιLev k i r' g))) ∧
      ∀ (w : List C.Letter), Fr.admitted st₀ (D.positionted w) → Fr.admitted st (D.positionted w) →
      ∀ (Ψ : Wd.Ix (Fin w.length) → RadSp k n z z' π π') (e : Wd.Ix (Fin w.length)) (c' : Fin r' → ℂ)
        (g : B.Mat k r'),
        (P5.act (Fr.ofWord L₀ st₀ (D.positionted w)).F Ψ e : Fn k n (Wq →L[ℂ] Wp)) c (D.castM hn (ιLev k i r' g)) =
          (P5.act (Fr.ofWord L st (D.positionted w)).F (fun e' => T (Ψ e')) e : Fn k r' (Wq →L[ℂ] Wp)) c' g := by
  subst hn
  rw [P.JCTx5.castV_rfl] at hz hz'
  subst hz hz'
  obtain rfl : πs = fun y => π (ιLev k i r' y) := funext fun y => by rw [hπ, P.JCTx5.castM_rfl]
  obtain rfl : πs' = fun y => π' (ιLev k i r' y) := funext fun y => by rw [hπ', P.JCTx5.castM_rfl]
  have fr := fun (j : Fin 6) v => fn_rs hr' hc X₀ X j v
  have tr := fun Y (a b : Fin 2) v => t_rs hr' hc X₀ X Y a b v
  obtain ⟨-, -, -, -, -, -, h0ζ, h0ζi, h0ζb, h0ζbi, h0G, h0Gi, h0TT⟩ := hL₀
  obtain ⟨-, -, -, -, -, -, hζ, hζi, hζb, hζbi, hG, hGi, hTT⟩ := hL
  have G : Gen (rsL hr' hc zs zs' π π') L₀ L :=
    { ζ := by rw [h0ζ, hζ]; exact rel_mk (fr 0) (fr 2)
      ζi := by rw [h0ζi, hζi]; exact rel_mk (fr 1) (fr 3)
      ζb := by rw [h0ζb, hζb]; exact rel_mk (fr 2) (fr 0)
      ζbi := by rw [h0ζbi, hζbi]; exact rel_mk (fr 3) (fr 1)
      GG := by rw [h0G, hG]; exact rel_mk (fr 4) (fr 4)
      GGi := by rw [h0Gi, hGi]; exact rel_mk (fr 5) (fr 5)
      TT := by rw [h0TT, hTT, tz_lift, tz_lift] }
  have hQ : ∀ Y, MRel (rsL hr' hc zs zs' π π') (st₀.QQ Y) (st.QQ Y) := fun Y => by
    rw [hst₀, hst]
    exact mrel_smul s fun a b => rel_mk (fun v => tr Y a b v) (fun v => tr (star Y) b a v)
  refine ⟨rsL hr' hc zs zs' π π', fun Ψ c' g => by rw [P.JCTx5.castM_rfl]; rfl, fun w h₀ h Ψ e c' g => ?_⟩
  rw [P.JCTx5.castM_rfl]
  have key := act_frame G hQ hq hinv hSL₀ hSL hs₀ hs (D.positionted w) h₀ h Ψ e
  exact congrArg (fun v : RadSp k r' zs zs' _ _ => (v : Fn k r' (Wq →L[ℂ] Wp)) c' g) key

end Formalism.FourierDecayAlt.P.WordCorrespondence

theorem Formalism.FourierDecayAlt.P.frame_transport_to_last_level : Formalism.FourierDecayAlt.P.PBI.FrameTransport := by
  intro Wp Wq _ _ _ _ _ _ P p X₀ μ₀ L₀ st₀ X μ L st hD₀ hD c hc
  obtain ⟨T, hT, hact⟩ := Formalism.FourierDecayAlt.P.WordCorrespondence.transport_gen P.k P.r P.r (P.r - P.r) (by omega) (by omega)
    (p.T.z_lev P.r le_rfl) (p.T.z'_lev P.r le_rfl) (p.T.π_lev P.r le_rfl) (p.T.π'_lev P.r le_rfl)
    X₀ L₀ st₀ X L st hD₀.2.2.1 hD.2.2.1 (Formalism.FourierDecayAlt.M.sgn P p.l0) hD₀.2.2.2.1 hD.2.2.2.1
    (hD₀.2.2.2.2.1.trans hD.2.2.2.2.1.symm) (hD₀.2.2.2.2.2.1.trans hD.2.2.2.2.2.1.symm)
    hD₀.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.1 hD₀.2.2.2.2.2.2.2 hD.2.2.2.2.2.2.2 c hc
  exact ⟨T, hT, fun w h₀ h Ψ e c' g _ _ => hact w h₀ h Ψ e c' g⟩
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadPictureEmptyWord
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

section read

variable {k : ℕ}

theorem pic_read {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n ρ : ℕ} (hn : 1 + ρ = n)
    {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * ρ + k + 1) → ℂ}
    (hz : z = D.castV hn (liftVec k 1 ρ zs)) (hz' : z' = D.castV hn (liftVec k 1 ρ zs'))
    (Φ : Fn k n E) (J : Mx k n → E)
    (hΦ : ∀ x ∈ DomR k n z z', Φ x.1 x.2 = resG k n (Fin.last n) J x.1 x.2)
    {t : ℂ} (ht : t ≠ 0) (y : (Fin ρ → ℂ) × Mx k ρ) (hy : y ∈ DomR k ρ zs zs') :
    Φ (fun l => PBH.consC t y.1 (Fin.cast hn.symm l)) (D.castM hn (ιLev k 1 ρ y.2)) =
      ((‖t‖ ^ (2 * n + k) : ℝ) : ℂ) •
        resG k ρ (Fin.last ρ) (fun γ => J (D.castM hn (U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ))) y.1 y.2 := by
  subst hn
  rw [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl] at hz hz'
  subst hz hz'
  simp only [Fin.cast_eq_self, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  rw [hΦ _ ((PBH.domR_iota ht zs zs' y.1 y.2).2 hy)]
  exact resG_consC ht J y.1 y.2

end read

def HeadPicNil : Prop :=
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (h : C.LPt) (hh : D.IsLocPt h j)
    (L : R.LevelData (Pr (Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π
      (p.T.bs j).π')) (JC.parLev P j).r)
    (Φ : Wd.Ix (Fin ([] : List C.Letter).length) →
      Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π'),
    KB.CptCoef p.T.base F →
    (∀ e, Top.IsRadOf (JC.parLev P j) (p.T.bs j) (Φ e) (KB.slv p.T F j (by omega) [] h hh.2 e)) →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin ([] : List C.Letter).length)),
    ∀ y ∈ Q.DomR P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z',
      (P5.act (P5.bTl L (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) (D.positionted [])) Φ e :
          Q.Fn (JC.parLev P j).k (JC.parLev P j).r (Wq →L[ℂ] Wp))
        (fun l => PBH.consC t y.1 (Fin.cast (by change P.r - j = 1 + (P.r - (j + 1)); omega) l))
          (D.castM (by change 1 + (P.r - (j + 1)) = P.r - j; omega) (ιLev P.k 1 (P.r - (j + 1)) y.2)) =
        ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) •
          Q.resG P.k (P.r - (j + 1)) (Fin.last _)
            (B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj [] (h ++ [(1, t)]) ht.2 e)) y.1 y.2

theorem headPic_nil (hS : KB.SliceStep) : HeadPicNil := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj h hh L Φ hF hΦ t ht e y hy
  have ht0 : t ≠ 0 := (ht.1 (1, t) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hn : 1 + (P.r - (j + 1)) = P.r - j := by omega

  have hact : P5.act (P5.bTl L (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) (D.positionted [])) Φ = Φ :=
    Formalism.FourierDecayAlt.P.PBF.polyAction_one₂ Φ
  rw [hact]
  have hread := pic_read (k := P.k) hn (PBH.levTower_bs_z_eq_castV_liftVec p.T j hj) (PBH.levTower_bs_z'_eq_castV_liftVec p.T j hj)
    (Subtype.val (Φ e)) (B.JF (p.T.bs j) (KB.slv p.T F j (by omega) [] h hh.2 e))
    (hΦ e) ht0 y hy
  refine hread.trans ?_
  congr 1
  unfold resG
  congr 1
  have hc : ∀ a, y.1 a ≠ 0 := hy.1
  have hγ := Formalism.FourierDecayAlt.P.PBF.wCell_mul_GV (i := Fin.last _) hc hy.2.1
  have hΩ := Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus (p.T.bs (j + 1)).z_mem (p.T.bs (j + 1)).z'_mem hy.1 hy.2.1 hy.2.2
  have he : e = fun a => a.elim0 := funext fun a => a.elim0
  subst he
  exact (hS Wp Wq P p F j hj h t hh ht hF _ hγ hΩ).symm

end Formalism.FourierDecayAlt.P.PBP

namespace Formalism.FourierDecayAlt.P

theorem head_picture_empty_word : PBP.HeadPicNil := PBP.headPic_nil slice_induction_level

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftCovarianceChartHolds
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix Polynomial
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem left_covariance_chart_holds : CovL := by
  intro k r d O U κ Φ hC x hx ξ Ξ₀ _hΞ₀ hcov X hX
  have hg : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
  obtain ⟨hgi, hig, hHg, hgH⟩ := gv_facts hg
  have hY : B.inLie k r ((κ x)⁻¹ * X * κ x) := by
    unfold B.inLie at hX ⊢

    have e1 : ((κ x)⁻¹ * X * κ x)ᴴ * Hpk k r = (κ x)ᴴ * (Xᴴ * Hpk k r) * κ x := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
      rw [← hHg]
    have e2 : Hpk k r * ((κ x)⁻¹ * X * κ x) = (κ x)ᴴ * (Hpk k r * X) * κ x := by
      simp only [← Matrix.mul_assoc]
      rw [← hgH]
    rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hX, Matrix.mul_zero, Matrix.zero_mul]
  have hV : VL κ Φ X x = VR κ Φ ((κ x)⁻¹ * X * κ x) x := by
    show fderiv ℝ Φ (κ x) (X * κ x) = fderiv ℝ Φ (κ x) (κ x * ((κ x)⁻¹ * X * κ x))
    rw [show κ x * ((κ x)⁻¹ * X * κ x) = X * κ x by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hig, Matrix.one_mul]]
  have ht : Matrix.trace (Ξ₀ * ((κ x)⁻¹ * X * κ x)) = Matrix.trace (κ x * Ξ₀ * (κ x)⁻¹ * X) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [hV, hcov _ hY, ht]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelTransport
section
open Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTieL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.PTieB

section id

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rel_id (A : Pr V) : Rel (LinearMap.id : V →ₗ[ℂ] V) A A :=
  ⟨by rw [LinearMap.comp_id, LinearMap.id_comp], by rw [LinearMap.comp_id, LinearMap.id_comp]⟩

theorem mrel_id (M : Matrix (Fin 2) (Fin 2) (Pr V)) : MRel (LinearMap.id : V →ₗ[ℂ] V) M M := fun _ _ => rel_id _

end id

theorem pairAt_smul {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : Measure (Mt k r)) (a : ℝ≥0)
    (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    P5.pairAt (a • μ) Φ Ψ c = ((a : ℝ) : ℂ) * P5.pairAt μ Φ Ψ c := by
  unfold P5.pairAt
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem glue_zero' {r : ℕ} (c : Fin r → ℂ) (c'' : Fin (r - 0) → ℂ) :
    P5.glue (⟨0, by omega⟩ : Fin (r + 1)) c (PTie.shiftCf ⟨0, by omega⟩ c'') = c'' := by
  funext l
  simp [P5.glue, PTie.shiftCf]

theorem glue_step {r : ℕ} (j : ℕ) (hj : j + 1 ≤ r) (c : Fin r → ℂ) (c'' : Fin (r - (j + 1)) → ℂ)
    (hn : r - j = 1 + (r - (j + 1))) :
    P5.glue (⟨j, by omega⟩ : Fin (r + 1)) c
        (PTie.shiftCf ⟨j, by omega⟩ (fun l => consC (c ⟨j, by omega⟩) c'' (Fin.cast hn l))) =
      P5.glue (⟨j + 1, by omega⟩ : Fin (r + 1)) c (PTie.shiftCf ⟨j + 1, by omega⟩ c'') := by
  funext l
  unfold P5.glue PTie.shiftCf consC
  by_cases h1 : j + 1 ≤ l.val
  · rw [dite_eq_left (show j ≤ l.val by omega), dite_eq_left h1]
    simp only [Fin.val_cast]
    rw [dite_eq_right (by omega)]
    congr 1
  · by_cases h2 : j ≤ l.val
    · rw [dite_eq_left h2, dite_eq_right h1]
      simp only [Fin.val_cast]
      rw [dite_eq_left (by omega)]
      congr 1
      ext
      simp only
      omega
    · rw [dite_eq_right h2, dite_eq_right h1]

theorem castM_iota0 {k r : ℕ} (h : 0 + (r - 0) = r) (g : B.Mat k (r - 0)) :
    D.castM h (ιLev k 0 (r - 0) g) = g := by
  ext p q
  simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, ιLev, finCongr_symm, finCongr_apply,
    Fin.val_cast]
  split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

theorem step_cast {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k n ρ : ℕ} (hn : n = 1 + ρ)
    {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * ρ + k + 1) → ℂ}
    (hz : z = D.castV hn.symm (liftVec k 1 ρ zs)) (hz' : z' = D.castV hn.symm (liftVec k 1 ρ zs'))
    (hzs : inWb k ρ zs) (hzs' : inWb k ρ zs')
    {π : Mx k n → (Wp →L[ℂ] Wp)} {π' : Mx k n → (Wq →L[ℂ] Wq)}
    {πs : Mx k ρ → (Wp →L[ℂ] Wp)} {πs' : Mx k ρ → (Wq →L[ℂ] Wq)}
    (hπ : ∀ y, πs y = π (D.castM hn.symm (ιLev k 1 ρ y))) (hπ' : ∀ y, πs' y = π' (D.castM hn.symm (ιLev k 1 ρ y)))
    (X : ActualOps k n z z' π π') (Xs : ActualOps k ρ zs zs' πs πs')
    (L : R.LevelData (Pr (RadSp k n z z' π π')) n) (st : Fr.Start (Pr (RadSp k n z z' π π')))
    (Ls : R.LevelData (Pr (RadSp k ρ zs zs' πs πs')) ρ) (sts : Fr.Start (Pr (RadSp k ρ zs zs' πs πs')))
    (s : ℂ) (μ : Measure (Mt k n)) (μs : Measure (Mt k ρ))
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (hst : ∀ Y, st.QQ Y = s • X.QQ Y)
    (hsts : ∀ Y, sts.QQ Y = s • Xs.QQ Y)
    (hμ : B.IsHaarOn (Glev k n (Fin.last n)) μ) (hμs : B.IsHaarOn (Glev k ρ (Fin.last ρ)) μs)
    (hlaw : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k n z z' (Fin.last n) (Matrix.of x)) ∂μ =
        ∫⁻ ζ, ENNReal.ofReal (B2.zWeight k (Tz k n z) (Tz k n z') ζ) * ψ ζ)
    (hlaws : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k ρ zs zs' (Fin.last ρ) (Matrix.of x)) ∂μs =
        ∫⁻ ζ, ENNReal.ofReal (B2.zWeight k (Tz k ρ zs) (Tz k ρ zs') ζ) * ψ ζ)
    (t : ℂ) (ht : t ≠ 0) :
    ∃ T : RadSp k n z z' π π' →ₗ[ℂ] RadSp k ρ zs zs' πs πs',
      (∀ Φ c g, (T Φ : Fn k ρ (Wq →L[ℂ] Wp)) c g =
        (Φ : Fn k n (Wq →L[ℂ] Wp)) (fun l => consC t c (Fin.cast hn l)) (D.castM hn.symm (ιLev k 1 ρ g))) ∧
      (∀ l : Fin ρ, Rel T (L.p ⟨l.val + 1, by omega⟩) (Ls.p l) ∧ Rel T (L.c ⟨l.val + 1, by omega⟩) (Ls.c l) ∧
        Rel T (L.ci ⟨l.val + 1, by omega⟩) (Ls.ci l)) ∧
      (∀ (m : ℕ) (hm : m ≤ ρ) (Y : ℂ),
        MRel T (P5.QQi L st ⟨m + 1, by omega⟩ Y) (P5.QQi Ls sts ⟨m, by omega⟩ Y)) ∧
      ∀ Φ Ψ c, P5.pairAt μs (T Φ) (T Ψ) c = P5.pairAt μ Φ Ψ (fun l => consC t c (Fin.cast hn l)) := by
  subst hn
  rw [P.JCTx5.castV_rfl] at hz hz'
  subst hz hz'
  obtain rfl : πs = fun y => π (ιLev k 1 ρ y) := funext fun y => by rw [hπ, P.JCTx5.castM_rfl]
  obtain rfl : πs' = fun y => π' (ιLev k 1 ρ y) := funext fun y => by rw [hπ', P.JCTx5.castM_rfl]
  rw [tz_iota, tz_iota] at hlaw
  have hmap : μs.map (B2.levM k ρ) = μ := map_levM_eq hμ hμs _ (zWeight_fin _ _) hlaw hlaws
  refine ⟨trL ht zs zs' π π', fun Φ c g => ?_, fun l => site_ops ht hL hLs l,
    fun m hm Y => qqi_rel_n ht hzs hzs' hL hLs hst hsts m hm Y, fun Φ Ψ c => ?_⟩
  · rw [P.JCTx5.castM_rfl]; rfl
  · exact pairAt_tr ht hmap Φ Ψ c

end Formalism.FourierDecayAlt.P.PTieL

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
end

