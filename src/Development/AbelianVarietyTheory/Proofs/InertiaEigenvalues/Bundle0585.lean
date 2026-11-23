module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0577
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0528
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameBreuilKisinDatumExists
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0543
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0564
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0574
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedValueTransitionBaseChange
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem eval_transition_comp_assoc {l : ℕ} {R : Type} [CommRing R] {P P' P'' P''' : Obj l R}
    (c : Hom P'' P''') (b : Hom P' P'') (a : Hom P P') : c.comp (b.comp a) = (c.comp b).comp a :=
  Hom.ext' rfl

theorem eval_transition : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B B' : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (N' : Type) [AddCommGroup N']
    [Module B'.A N'] (V : Eval S B N) (V' : Eval S B' N') (k : Hom B B'),
    ∃ t : N →ₛₗ[k.f] N', SemiBC t ∧ ∀ (Q : Obj l ↥(OL K)) (a : Hom B' Q) (g : Hom bk.prism Q) (x : N),
      V'.v a g (t x) = V.v (a.comp k) g x := by
  intro l _ K bk d S B B' N _ _ N' _ _ V V' k
  obtain ⟨C', h', ⟨f'⟩, hc⟩ := _root_.GlobalTheory.BSP.exists_cover_receiving_bk l K bk B'
  obtain ⟨hinj, hsurj⟩ := _root_.GlobalTheory.BSP.Eval.effective_of_cover l K bk d S B' C' N' V' h' f' hc
  have hz : ∀ x : N, ∃ y, V'.v h' f' y = V.v (h'.comp k) f' x := by
    intro x
    apply hsurj
    intro Q p q hpq
    have e : p.comp (h'.comp k) = q.comp (h'.comp k) := by
      rw [eval_transition_comp_assoc, hpq, ← eval_transition_comp_assoc]
    have hp : (fun i => p.f (V.v (h'.comp k) f' x i)) = V.v (p.comp (h'.comp k)) (p.comp f') x :=
      funext fun i => (V.v_nat p (h'.comp k) f' x i).symm
    have hq : (fun i => q.f (V.v (h'.comp k) f' x i)) = V.v (q.comp (h'.comp k)) (q.comp f') x :=
      funext fun i => (V.v_nat q (h'.comp k) f' x i).symm
    rw [hp, hq, V.v_ε (p.comp (h'.comp k)) (p.comp f') (q.comp f') x, e]
  choose t0 ht0 using hz
  let t : N →ₛₗ[k.f] N' :=
    { toFun := t0
      map_add' := fun x y => hinj <|
        (ht0 (x + y)).trans ((LinearMap.map_add (V.v (h'.comp k) f') x y).trans
          ((congrArg₂ (· + ·) (ht0 x) (ht0 y)).symm.trans (LinearMap.map_add (V'.v h' f') (t0 x) (t0 y)).symm))
      map_smul' := fun c x => hinj <|
        (ht0 (c • x)).trans ((LinearMap.map_smulₛₗ (V.v (h'.comp k) f') c x).trans
          ((congrArg (h'.f (k.f c) • ·) (ht0 x)).symm.trans (LinearMap.map_smulₛₗ (V'.v h' f') (k.f c) (t0 x)).symm)) }
  have hT : ∀ x, V'.v h' f' (t x) = V.v (h'.comp k) f' x := ht0
  refine ⟨t, ?_, ?_⟩
  · haveI := V.fin; haveI := V.proj; haveI := V'.fin; haveI := V'.proj
    exact _root_.GlobalTheory.BSP.semiBC_of_cover l (↥(OL K)) B' C' h' hc B.A k.f N N' (Fin d → C'.A) t (V'.v h' f')
      (V.v (h'.comp k) f') (fun x => (hT x).symm) (V'.bc h' f') (V.bc (h'.comp k) f')
  · intro Q a g x
    obtain ⟨Q'', h'', a', hsq, hinj''⟩ := _root_.GlobalTheory.BSP.cover_po_injective l K bk d S B' C' h' hc Q a
    have e2 : h''.comp (a.comp k) = a'.comp (h'.comp k) := by
      rw [eval_transition_comp_assoc, ← hsq, ← eval_transition_comp_assoc]
    have key : V'.v (a'.comp h') (a'.comp f') (t x) = V.v (a'.comp (h'.comp k)) (a'.comp f') x :=
      funext fun j => (V'.v_nat a' h' f' (t x) j).trans ((congrArg a'.f (congrFun (hT x) j)).trans (V.v_nat a' (h'.comp k) f' x j).symm)
    funext i
    apply hinj''
    calc h''.f (V'.v a g (t x) i) = V'.v (h''.comp a) (h''.comp g) (t x) i := (V'.v_nat h'' a g (t x) i).symm
      _ = V'.v (a'.comp h') (h''.comp g) (t x) i := congrArg (fun c => V'.v c (h''.comp g) (t x) i) hsq.symm
      _ = (S.ε (h''.comp g) (a'.comp f')).mulVec (V'.v (a'.comp h') (a'.comp f') (t x)) i :=
          congrFun (V'.v_ε (a'.comp h') (h''.comp g) (a'.comp f') (t x)) i
      _ = (S.ε (h''.comp g) (a'.comp f')).mulVec (V.v (a'.comp (h'.comp k)) (a'.comp f') x) i :=
          congrArg (fun w => (S.ε (h''.comp g) (a'.comp f')).mulVec w i) key
      _ = V.v (a'.comp (h'.comp k)) (h''.comp g) x i :=
          (congrFun (V.v_ε (a'.comp (h'.comp k)) (h''.comp g) (a'.comp f') x) i).symm
      _ = V.v (h''.comp (a.comp k)) (h''.comp g) x i := congrArg (fun c => V.v c (h''.comp g) x i) e2.symm
      _ = h''.f (V.v (a.comp k) g x i) := V.v_nat h'' (a.comp k) g x i

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionClassEqLPowSmulGalois
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.ExtClass

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e}
  {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]
  {T Tp U : LocLat (Gl l) ℚ_[l] K O} {f : LatHom T.L Tp.L} {g : LatHom Tp.L U.L}


omit [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in
theorem map_injective (hfg : IsSESLat (Qp := ℚ_[l]) f g) (B : Type) [AddCommGroup B] [Module O B] :
    Function.Injective (TensorProduct.map (LinearMap.id : B →ₗ[O] B) ((f.f.restrictScalars O).restrict f.T_le)) := by
  obtain ⟨h1, -, h3, h4, h5⟩ := hfg
  have := U.L.free
  refine LinearMap.lTensor_injective_of_exact_of_flat ((g.f.restrictScalars O).restrict g.T_le) (fun z => ?_)
    ((f.f.restrictScalars O).restrict f.T_le) (fun x y h => Subtype.ext (h1 (congrArg Subtype.val h)))
    (fun z => ⟨fun h => ?_, ?_⟩) B
  · obtain ⟨x, hx, h⟩ := h3 z.1 z.2
    exact ⟨⟨x, hx⟩, Subtype.ext h⟩
  · obtain ⟨y, hy⟩ := (h4 z.1).1 (congrArg Subtype.val h)
    exact ⟨⟨y, h5 y (hy ▸ z.2)⟩, Subtype.ext hy⟩
  · rintro ⟨y, rfl⟩
    exact Subtype.ext ((h4 _).2 ⟨y.1, rfl⟩)

theorem exists_solution {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {R : PhiMod O K l e a μ}
    {I : Ident t ϖ P T} {Ip : Ident t ϖ Q Tp} {Iu : Ident t ϖ R U} {F : GlobalTheory.BK.Hom P Q} {G : GlobalTheory.BK.Hom Q R}
    (hfg : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I Ip f F) (hG : IsMapOf Ip Iu g G) (u : ME R) (x : ↥U.L.T)
    (hux : toW t ϖ R u = Iu.ofT x) (k : ℕ) {x₂ : Vec K a κ} (hx₂ : x₂ ∈ Q.M) (hGx : G.app x₂ = k • u.1)
    (v : ↥Tp.L.T) (hv : g.f v = x.1) {y : Vec K a ι} (hy : y ∈ ME P) (hFy : F.app y = Q.phi x₂ - x₂) :
    ∃ m₀, phiW t ϖ P m₀ - m₀ = toW t ϖ P ⟨y, hy⟩ ∧
      homW t ϖ F m₀ = toW t ϖ Q ⟨x₂, mem_ME_of_mem_M hx₂⟩ - k • Ip.ofT v := by
  obtain ⟨m₁, hm₁⟩ := I.exists_phiW_sub (toW t ϖ P ⟨y, hy⟩)
  have hfixp : ∀ z, phiW t ϖ Q (Ip.ofT z) = Ip.ofT z := fun z =>
    mem_Treal.1 (by rw [← Ip.range_ofT]; exact ⟨z, rfl⟩)
  have hfix : ∀ z, phiW t ϖ P (I.ofT z) = I.ofT z := fun z =>
    mem_Treal.1 (by rw [← I.range_ofT]; exact ⟨z, rfl⟩)
  have h1 : phiW t ϖ Q (homW t ϖ F m₁) - homW t ϖ F m₁ =
      phiW t ϖ Q (toW t ϖ Q ⟨x₂, mem_ME_of_mem_M hx₂⟩) - toW t ϖ Q ⟨x₂, mem_ME_of_mem_M hx₂⟩ := by
    rw [← homW_phiW, ← map_sub, hm₁, homW_toW, ← toW_phi t ϖ Q hx₂, ← map_sub]
    exact congrArg _ (Subtype.ext hFy)
  have h2 : homW t ϖ F m₁ - (toW t ϖ Q ⟨x₂, mem_ME_of_mem_M hx₂⟩ - k • Ip.ofT v) ∈ LinearMap.range Ip.ofT := by
    rw [Ip.range_ofT, mem_Treal, map_sub, map_sub, map_nsmul, hfixp, sub_eq_iff_eq_add.1 h1]
    abel
  obtain ⟨z, hz⟩ := h2
  have h3 : homW t ϖ G (homW t ϖ F m₁) = 0 := by
    apply Iu.j.injective
    rw [hG, hF, map_zero]
    induction I.j m₁ using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul w s =>
      have h0 : ((g.f.restrictScalars O).restrict g.T_le) (((f.f.restrictScalars O).restrict f.T_le) s) = 0 :=
        Subtype.ext ((hfg.2.2.2.1 _).2 ⟨s.1, rfl⟩)
      simp only [latW, TensorProduct.map_tmul, h0, TensorProduct.tmul_zero]
    | add p q hp hq => simp only [map_add (f := _), hp, hq, add_zero]
  have h4 : homW t ϖ G (toW t ϖ Q ⟨x₂, mem_ME_of_mem_M hx₂⟩) = k • Iu.ofT x := by
    rw [homW_toW, ← hux, ← map_nsmul]
    exact congrArg _ (Subtype.ext hGx)
  have h5 : homW t ϖ G (Ip.ofT v) = Iu.ofT x := by
    rw [hG.homW_ofT]
    exact congrArg _ (Subtype.ext hv)
  have h6 := congrArg (homW t ϖ G) hz
  rw [map_sub, map_sub, map_nsmul, h3, h4, h5, sub_self, sub_self, hG.homW_ofT, ← map_zero Iu.ofT] at h6
  obtain ⟨s, hs⟩ := (hfg.2.2.2.1 z.1).1 (congrArg Subtype.val (Iu.ofT_injective h6))
  have hsT : s ∈ T.L.T := hfg.2.2.2.2 s (hs ▸ z.2)
  refine ⟨m₁ - I.ofT ⟨s, hsT⟩, ?_, ?_⟩
  · rw [map_sub, hfix, ← hm₁]
    abel
  · rw [map_sub, hF.homW_ofT, show (⟨f.f (⟨s, hsT⟩ : ↥T.L.T), f.T_le _ hsT⟩ : ↥Tp.L.T) = z from Subtype.ext hs, hz]
    abel

theorem isCrisVal_toW {P : PhiMod O K l e a ι} (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) {w : Vec K a ι}
    (hL : w ∈ P.L) (hS : w ∈ P.MMl) :
    IsCrisVal t ϖ P jB (toW t ϖ P ⟨w, mem_ME_of_mem_L hL⟩) (jB (toBcris t ϖ P ⟨w, hS⟩)) := by
  refine ⟨1, fun i => ϖ.iTot t K (GlobalTheory.BKReal.coordL P (GlobalTheory.BK.A O K) ⟨_, hL⟩ i), by rw [map_one]; exact isUnit_one, ?_, ?_⟩
  · rw [map_one, one_smul]
    exact (toW_toCris_of_mem_L t ϖ P hL (P.ext_mono (A_le_S l e) hL)).1
  · rw [map_one, one_smul]
    refine congrArg _ (funext fun i => ?_)
    rw [toBcris_apply, toB, AlgHom.comp_apply, ← ϖ.iC_of_mem t K, ← ϖ.iB_of_mem t K]
    rfl

variable [TameDescentExponentData K l e a] {η H : ℕ}


set_option maxHeartbeats 1600000 in
theorem classOf {D : BKDat O K l e a ι η H} {Dp : BKDat O K l e a κ η H} {Du : BKDat O K l e a μ η H}
    (R : GalDat t ϖ (sQ l) D T) (Rp : GalDat t ϖ (sQ l) Dp Tp) (Ru : GalDat t ϖ (sQ l) Du U)
    (F : BKHom D Dp) (G : BKHom Dp Du) (hfg : IsSESLat (Qp := ℚ_[l]) f g)
    (hF : IsMapOf R.I Rp.I f F.toHom) (hG : IsMapOf Rp.I Ru.I g G.toHom) (hinj : Function.Injective F.app)
    (u : ME Du.toPhiMod) (x : ↥U.L.T) (hux : toW t ϖ Du.toPhiMod u = Ru.I.ofT x) (n : ℕ) {x₂ : Vec K a κ}
    (hx₂ : x₂ ∈ Dp.Minv) (hGx : G.app x₂ = (l ^ n) • u.1) {v : Tp.V} {c : Gl l → T.V} (hv : v ∈ Tp.L.T)
    (hgv : g.f v = x.1) (hc : ∀ h, Tp.ρ h v - v = f.f (c h)) {σ : Vec K a ι} (hσ : σ ∈ D.MMl)
    (hσi : σ ∈ D.desc.inv) (hFσ : F.app σ = Dp.phi x₂ - Dp.xi (red (Dp.phi x₂))) {y : Vec K a ι} (hy : y ∈ D.Y)
    (hFy : F.app y = Dp.phi x₂ - x₂) : R.ClassOf y ((l : K) ^ n • c) := by
  have hyE : y ∈ ME D.toPhiMod := BKDat.mem_invE_of_mem_Y hy
  obtain ⟨m₀, hm₀, hFm₀⟩ := exists_solution hfg hF hG u x hux (l ^ n) hx₂.1 hGx ⟨v, hv⟩ hgv hyE hFy
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.GalPot.exists_isCrisVal R hy hyE m₀ hm₀
  have hz : D.conn σ = D.zeta y := by
    apply hinj
    rw [F.toHom.app_conn, F.toHom.app_zeta, hFσ, hFy, PhiMod.zeta_phi_sub, map_sub, PhiMod.conn_xi, sub_zero]
  refine ⟨_, ⟨hyE, m₀, ⟨σ, hσ⟩, b₀, hm₀, hσi, hz, hb₀, rfl⟩, ?_⟩
  have hAS : A O K ≤ invL l (S O K e) := (A_le_S l e).trans (le_away _ _)
  have hL := Dp.phi_mem_L hx₂.1
  have hS : Dp.phi x₂ ∈ Dp.MMl := Dp.ext_mono hAS hL
  have hFS : F.app σ ∈ Dp.MMl := F.toHom.app_mem_ext hAS hσ
  have hξ : Dp.xi (red (Dp.phi x₂)) ∈ Dp.MMl := by
    have := sub_mem hS hFS
    rwa [hFσ, sub_sub_cancel] at this
  have hfixξ := GlobalTheory.GalPot.fix_of_horiz Rp ⟨_, hξ⟩ (fun γ => by
    change Dp.desc.act γ (Dp.xi _) = Dp.xi _
    rw [Descent.act_xi, ← Descent.red_act, Dp.desc.act_phi, hx₂.2 γ]) (Dp.conn_xi _)
  have N := _root_.GlobalTheory.BKGal.cris_natural l a e O K t ϖ ι D.toPhiMod T R.I R.jB R.cmp κ Dp.toPhiMod Tp Rp.I Rp.jB f
    F.toHom Rp.cmp hF
  have C := (_root_.GlobalTheory.CrisComparison.main l a e O K t ϖ κ Dp.toPhiMod Tp Rp.I).2 Rp.jB Rp.cmp
  set Φ := TensorProduct.map (R := O) (LinearMap.id (R := O) (M := OB l O))
    ((f.f.restrictScalars O).restrict f.T_le) with hΦ
  have hfix : phiW t ϖ Dp.toPhiMod (Rp.I.ofT ⟨v, hv⟩) = Rp.I.ofT ⟨v, hv⟩ :=
    mem_Treal.1 (by rw [← Rp.I.range_ofT]; exact ⟨_, rfl⟩)
  have h1 := N.2 _ _ hb₀
  rw [homW_phiW, hFm₀, map_sub, map_nsmul, hfix, ← toW_phi t ϖ Dp.toPhiMod hx₂.1] at h1
  have h2 := C.2.1 _ _ _ h1 (IsCrisVal.sub t ϖ (isCrisVal_toW Rp.jB hL hS)
    (GlobalTheory.GalPot.isCrisVal_nsmul (C.2.2.2.1 ⟨v, hv⟩) (l ^ n)))
  have h3 : Φ (R.jB (toBcris t ϖ D.toPhiMod ⟨σ, hσ⟩) - b₀) =
      (l ^ n) • ((1 : OB l O) ⊗ₜ[O] (⟨v, hv⟩ : ↥Tp.L.T)) - Rp.jB (toBcris t ϖ Dp.toPhiMod ⟨_, hξ⟩) := by
    rw [map_sub, h2, ← N.1 ⟨σ, hσ⟩ ⟨_, hFS⟩ rfl,
      show (⟨F.app σ, hFS⟩ : Dp.MMl) = ⟨_, hS⟩ - ⟨_, hξ⟩ from Subtype.ext hFσ, map_sub, map_sub]
    abel
  intro γ k s hs
  apply map_injective hfg (OB l O)
  have hact : actB (sQ l) Tp γ ((1 : OB l O) ⊗ₜ[O] (⟨v, hv⟩ : ↥Tp.L.T)) =
      (1 : OB l O) ⊗ₜ[O] (Tp.actT γ ⟨v, hv⟩) := by
    rw [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]
  have hs' : (f.f.restrictScalars O).restrict f.T_le s = (l : O) ^ k • (l : O) ^ n • (Tp.actT γ ⟨v, hv⟩ - ⟨v, hv⟩) := by
    have hsm : ∀ (j : ℕ) (w : Tp.V), ((l : O) ^ j) • w = (l : K) ^ j • w := fun j w => by
      rw [← algebraMap_smul K ((l : O) ^ j) w, map_pow, map_natCast]
    apply Subtype.ext
    change f.f (s : T.V) = (l : O) ^ k • (l : O) ^ n • (Tp.ρ γ v - v)
    rw [hs, hsm, hsm, hc, Pi.smul_apply, map_smul, map_smul]
  rw [map_smul, map_sub, GlobalTheory.CocycleNat.actB_map, ← hΦ, h3, map_sub, map_nsmul, hfixξ, hact, hΦ,
    TensorProduct.map_tmul, LinearMap.id_apply, hs', TensorProduct.tmul_smul, TensorProduct.tmul_smul,
    TensorProduct.tmul_sub, smul_sub, ← Nat.cast_smul_eq_nsmul O, ← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
  congr 1
  abel


set_option maxHeartbeats 1000000 in
theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (η H : ℕ) (T Tp : QLat LL) (f : LatHom T.L Tp.L) (g : LatHom Tp.L (unitLat (Gl l) : QLat LL).L), IsSESLat (Qp := ℚ_[l]) f g → ∀ (Pk : Pack a ϖ η H T) (Pp : Pack a ϖ η H Tp) (Pu : Pack a ϖ η H (unitLat (Gl l) : QLat LL)) (F : BKHom Pk.D Pp.D) (G : BKHom Pp.D Pu.D), IsMapOf Pk.R.I Pp.R.I f F.toHom → IsMapOf Pp.R.I Pu.R.I g G.toHom → IsExactTriple F.toHom G.toHom → Function.Injective F.app → ∀ (u : ME Pu.D.toPhiMod) (x : ↥(unitLat (Gl l) : QLat LL).L.T), x.1 = (1 : ↥LL.1) → u.1 ∈ Pu.D.Minv → Pu.D.phi u.1 = u.1 → toW (thetaW a LL) ϖ Pu.D.toPhiMod u = Pu.R.I.ofT x → ∀ (n : ℕ) (x₂ : Vec ↥LL.1 a (Fin Pp.n)), x₂ ∈ Pp.D.Minv → G.app x₂ = (l ^ n) • u.1 → ∀ (v : Tp.V) (c : Gl l → T.V), v ∈ Tp.L.T → g.f v = (1 : ↥LL.1) → (∀ h, Tp.ρ h v - v = f.f (c h)) → ∀ σ ∈ Pk.D.MMl, σ ∈ Pk.D.desc.inv → F.app σ = Pp.D.phi x₂ - Pp.D.xi (red (Pp.D.phi x₂)) → ∀ y ∈ Pk.D.Y, F.app y = Pp.D.phi x₂ - x₂ → Pk.R.ClassOf y ((l : ↥LL.1) ^ n • c) := by
  intro l _ a e _ _ ϖ LL _ _ η H T Tp f g hfg Pk Pp Pu F G hF hG _ hinj u x hx1 _ _ hux n x₂ hx₂ hGx₂ v c hv hgv hc σ hσ hσi hFσ y hy hFy
  exact classOf Pk.R Pp.R Pu.R F G hfg hF hG hinj u x hux n hx₂ hGx₂ hv (hgv.trans hx1.symm) hc hσ hσi hFσ hy hFy

end GlobalTheory.ExtClass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionSubMemFiltrationZeroOfMonodromy
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem GlobalTheory.BKGal.gb_sub_b_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g b - b ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R y hyY hMon b hb g hg
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  refine ⟨C, ?_⟩
  obtain ⟨hy, m₀, σ, b₀, h1, h2, h3, h4, rfl⟩ := hb
  obtain ⟨b₁, hb₁, hF⟩ := _root_.GlobalTheory.BKGal.value_mem_filtration_zero l a e O K t ϖ hl2 ι η H D T R y hyY hy m₀ h1
  have hv : IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) (b₀ - b₁) := by
    rw [← h1]; exact GlobalTheory.BKGal.IsCrisVal.sub t ϖ h4 hb₁
  have h5 := _root_.GlobalTheory.BKGal.gal_sub_value_sigma_sub_y_mem_filZero l a e O K t ϖ hl2 ι η H D T R y hyY hMon hy σ h2 h3 (b₀ - b₁) hv g hg C
  have h6 := hF g hg C
  have h7 := Submodule.sub_mem _ h5 h6
  convert h7 using 1
  simp only [map_sub]
  abel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenCuspidalCharsByRegularCharsProof
section
noncomputable section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GreenRegularCharactersInertiaEigenvalues

variable {g : ℕ} [Fact g.Prime]

theorem isPrimeLab_pos {e : ℕ} {P : (ZMod g)[X]} (h : IsPrimeLab e P) : 0 < e := by
  have := degree_pos_of_irreducible h.2.1
  rw [← h.2.2.2]
  exact natDegree_pos_iff_degree_pos.mpr this

theorem family (g : ℕ) [Fact g.Prime] (e : ℕ) (he : 0 < e) (K : Type) [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = e) (τ : (Kˣ →* ℂˣ) → Gn g e → ℂ)
    (h1 : ∀ θ, IsRegularChar g e θ → IsCusp (τ θ))
    (h2 : ∀ θ θ', IsRegularChar g e θ → IsRegularChar g e θ' → (τ θ = τ θ' ↔ ∃ i < e, θ' = θ ^ g ^ i)) :
    ∃ L : (ZMod g)[X] → Gn g e → ℂ,
      (∀ P, IsPrimeLab e P → IsCusp (L P) ∧ ∃ θ, IsRegularChar g e θ ∧ L P = τ θ) ∧
      ∀ P P', IsPrimeLab e P → IsPrimeLab e P' → L P = L P' → P = P' := by
  obtain ⟨c, hc1, hc2⟩ := _root_.GlobalTheory.PrimeLabOrbit.primeLab_to_regularChar g e he K hK
  refine ⟨fun P => τ (c P), fun P hP => ⟨h1 _ (hc1 P hP), c P, hc1 P hP, rfl⟩, ?_⟩
  intro P P' hP hP' h
  exact hc2 P P' hP hP' ((h2 _ _ (hc1 P hP) (hc1 P' hP')).mp h)

theorem factor_lab {f : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0) :
    ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors f, IsPrimeLab P.natDegree P := by
  intro P hP
  have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP
  have hmon : P.Monic := by
    rw [← UniqueFactorizationMonoid.normalize_normalized_factor P hP]
    exact monic_normalize hirr.ne_zero
  refine ⟨hmon, hirr, ?_, rfl⟩
  intro hc
  have : (X : (ZMod g)[X]) ∣ f :=
    (X_dvd_iff.mpr hc).trans (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)
  exact h0 (X_dvd_iff.mp this)

theorem prod_factors {f : (ZMod g)[X]} (hf : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    (UniqueFactorizationMonoid.normalizedFactors f).prod = f := by
  have hm : ((UniqueFactorizationMonoid.normalizedFactors f).prod).Monic := by
    have := monic_multiset_prod_of_monic (UniqueFactorizationMonoid.normalizedFactors f) id
      (fun P hP => (factor_lab h0 P hP).1)
    simpa using this
  exact eq_of_monic_of_associated hm hf (UniqueFactorizationMonoid.prod_normalizedFactors hf.ne_zero)

theorem count (d : ℕ) (hd : 0 < d) (Lf : ∀ e, (ZMod g)[X] → Gn g e → ℂ)
    (hc : ∀ e P, IsPrimeLab e P → IsCusp (Lf e P))
    (hi : ∀ e P P', IsPrimeLab e P → IsPrimeLab e P' → Lf e P = Lf e P' → P = P')
    (χ : Gn g d → ℂ) (hχ : IsCusp χ) (hne : ∀ P, IsPrimeLab d P → Lf d P ≠ χ) : False := by
  let s : Set (ZMod g)[X] := {P | IsPrimeLab P.natDegree P}
  let φ : (ZMod g)[X] → Pc g := fun P => ⟨P.natDegree, Lf P.natDegree P⟩
  have hinj : Set.InjOn φ s := by
    intro P hP P' hP' h
    have h1 : P.natDegree = P'.natDegree := congrArg Sigma.fst h
    have h2 : (⟨P'.natDegree, Lf P'.natDegree P'⟩ : Pc g) = ⟨P.natDegree, Lf P.natDegree P'⟩ := by rw [h1]
    have h3 : Lf P.natDegree P = Lf P.natDegree P' := sigma_mk_injective (h.trans h2)
    have hP'' : IsPrimeLab P.natDegree P' := by rw [h1]; exact hP'
    exact hi _ P P' hP hP'' h3
  let ψ : Pc g → (ZMod g)[X] := Function.invFunOn φ s
  have hleft : ∀ P ∈ s, ψ (φ P) = P := fun P hP => hinj.leftInvOn_invFunOn hP
  let T : Set (ZMod g)[X] := {f | f.Monic ∧ f.natDegree = d ∧ f.coeff 0 ≠ 0}
  obtain ⟨hcard, hfin⟩ := _root_.GlobalTheory.GrPolys.card_monic_coeff_zero_ne_zero g d hd
  let F : (ZMod g)[X] → Multiset (Pc g) := fun f => (UniqueFactorizationMonoid.normalizedFactors f).map φ
  have hback : ∀ f ∈ T, (F f).map ψ = UniqueFactorizationMonoid.normalizedFactors f := by
    intro f hf
    simp only [F, Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id (UniqueFactorizationMonoid.normalizedFactors f)]
    exact Multiset.map_congr rfl (fun P hP => hleft P (factor_lab hf.2.2 P hP))
  have hFinj : Set.InjOn F T := by
    intro f hf f' hf' h
    have := congrArg (fun M => (M.map ψ).prod) h
    simp only [hback f hf, hback f' hf'] at this
    rwa [prod_factors hf.1 hf.2.2, prod_factors hf'.1 hf'.2.2] at this
  have hnot : ({⟨d, χ⟩} : Multiset (Pc g)) ∉ hfin.toFinset.image F := by
    intro hmem
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp hmem
    rw [Set.Finite.mem_toFinset] at hf
    have hnf := hback f hf
    rw [hfe, Multiset.map_singleton] at hnf
    have hPmem : ψ ⟨d, χ⟩ ∈ UniqueFactorizationMonoid.normalizedFactors f := by
      rw [← hnf]; exact Multiset.mem_singleton_self _
    have hPl := factor_lab hf.2.2 _ hPmem
    have hφ : φ (ψ ⟨d, χ⟩) = ⟨d, χ⟩ := by
      have := hfe
      simp only [F] at this
      rw [← hnf, Multiset.map_singleton, Multiset.singleton_inj] at this
      exact this
    set P := ψ ⟨d, χ⟩ with hPdef
    have hdeg : P.natDegree = d := congrArg Sigma.fst hφ
    have h2 : (⟨d, Lf d P⟩ : Pc g) = ⟨P.natDegree, Lf P.natDegree P⟩ := by rw [hdeg]
    have h3 : Lf d P = χ := sigma_mk_injective (h2.trans hφ)
    have hPl' : IsPrimeLab d P := by rw [← hdeg]; exact hPl
    exact hne P hPl' h3
  let S : Finset (Multiset (Pc g)) := insert {⟨d, χ⟩} (hfin.toFinset.image F)
  have hS : ∀ M ∈ S, (M.map fun p => p.1).sum = d ∧ ∀ p ∈ M, IsCusp p.2 := by
    intro M hM
    rcases Finset.mem_insert.mp hM with rfl | hM
    · refine ⟨by simp, ?_⟩
      intro p hp
      rw [Multiset.mem_singleton] at hp
      subst hp
      exact hχ
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hM
      rw [Set.Finite.mem_toFinset] at hf
      refine ⟨?_, ?_⟩
      · simp only [F, Multiset.map_map]
        have hdeg := natDegree_multiset_prod_of_monic (UniqueFactorizationMonoid.normalizedFactors f)
          (fun P hP => (factor_lab hf.2.2 P hP).1)
        rw [prod_factors hf.1 hf.2.2, hf.2.1] at hdeg
        rw [hdeg]
        rfl
      · intro p hp
        obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hp
        exact hc _ P (factor_lab hf.2.2 P hP)
  have hle := _root_.GlobalTheory.GLq.CuspMultisetCount.card_le g d hd S hS
  have hcardS : S.card = g ^ d - g ^ (d - 1) + 1 := by
    rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn, ← hcard,
      Set.ncard_eq_toFinset_card T hfin]
    rw [Set.Finite.coe_toFinset]
    exact hFinj
  omega

end GlobalTheory.GreenRegularCharactersInertiaEigenvalues


open GlobalTheory.GreenRegularCharactersInertiaEigenvalues in
theorem GlobalTheory.greenRegularCharacters_holds : GreenRegularCharacters := by
  intro g _ d hd K _ _ hK
  obtain ⟨τ, hτ1, hτ2⟩ := _root_.GlobalTheory.GreenRegular.exists_cusp_of_regular g d hd K hK
  refine ⟨τ, hτ1, hτ2, ?_⟩
  have hex : ∀ e, ∃ L : (ZMod g)[X] → Gn g e → ℂ,
      (∀ P, IsPrimeLab e P → IsCusp (L P)) ∧
      (∀ P P', IsPrimeLab e P → IsPrimeLab e P' → L P = L P' → P = P') ∧
      (∀ _ : e = d, ∀ P, IsPrimeLab e P → ∃ θ, IsRegularChar g d θ ∧ (⟨e, L P⟩ : Pc g) = ⟨d, τ θ⟩) := by
    intro e
    by_cases hed : e = d
    · subst hed
      obtain ⟨L, hL1, hL2⟩ := family g e hd K hK τ (fun θ hθ => (hτ1 θ hθ).1) hτ2
      refine ⟨L, fun P hP => (hL1 P hP).1, hL2, fun _ P hP => ?_⟩
      obtain ⟨θ, hθ, he⟩ := (hL1 P hP).2
      exact ⟨θ, hθ, by rw [he]⟩
    · by_cases he0 : e = 0
      · refine ⟨fun _ _ => 0, fun P hP => absurd (isPrimeLab_pos hP) (by omega),
          fun P _ hP _ _ => absurd (isPrimeLab_pos hP) (by omega), fun h => absurd h hed⟩
      · have hpos : 0 < e := Nat.pos_of_ne_zero he0
        obtain ⟨τ', hτ'1, hτ'2⟩ := _root_.GlobalTheory.GreenRegular.exists_cusp_of_regular g e hpos (GaloisField g e) (GaloisField.finrank g he0)
        obtain ⟨L, hL1, hL2⟩ := family g e hpos (GaloisField g e) (GaloisField.finrank g he0) τ'
          (fun θ hθ => (hτ'1 θ hθ).1) hτ'2
        exact ⟨L, fun P hP => (hL1 P hP).1, hL2, fun h => absurd h hed⟩
  choose Lf hc hi hdd using hex
  intro χ hχ
  by_contra hno
  push_neg at hno
  refine count d hd Lf hc hi χ hχ ?_
  intro P hP heq
  obtain ⟨θ, hθ, hs⟩ := hdd d rfl P hP
  have : Lf d P = τ θ := sigma_mk_injective hs
  exact hno θ hθ (heq ▸ this)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCocyclesMemSpanPushoutSummandLatticeStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCocycles_mem_span_pushout_summandLattice : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))),
    GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M)
      (F : Finset (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)),
      (F : Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)) ⊆ cutCoc i w hw r Xs M →
      ∃ X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw),
        IsSummandTw i w hw r Xs X ∧
        Submodule.span (Br.OLL D.nbr i w hw) (F : Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)) ≤
          BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) X (locU i w hw M hSub.1) (Br.locLat D.nbr i w hw M) := by
  first | exact @GlobalTheory.Pass.LocDual.OneX.main | exact GlobalTheory.Pass.LocDual.OneX.main | (intros; apply GlobalTheory.Pass.LocDual.OneX.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeedCoeffRecurrenceStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seed_coeff_recurrence_alt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → ∀ (cD : ι → (bk.DA bk.ρ₀ →+ bk.DS bk.ρ₀)), (∀ i a, cD i (bk.iA a) = toDisc l (X : bk.S) bk.ρ₀ (TB.c i a)) → (∀ i x y, cD i (j x * y) = x * cD i y) → (∀ y, HasSum (fun i => j (cD i y) * bk.iA (TB.b i)) y) → (∀ i y, ‖cD i y‖ ≤ ‖y‖) → ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → ∀ (i₁ : ι) (a b : Fin d), HasSum (fun i => Φ ((s.W * (s.W'.map (cD i)).map j) a b) * bk.iS (TB.c i₁ (WittVector.frobenius (TB.b i)))) (bk.iS bk.E ^ (2 * s.N) * (s.W * (s.W'.map (cD i₁)).map j) a b) := by
  first | exact @GlobalTheory.BSP.seed_coeff_recurrence | exact GlobalTheory.BSP.seed_coeff_recurrence | (intros; apply GlobalTheory.BSP.seed_coeff_recurrence <;> assumption)
end

