module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.UaFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.FinOrbSubgroupOf
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open GlobalTheory.SplitWeil
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

private theorem finOrb_subgroupOf {G : Type} [Group G] (H J : Subgroup G) (d : H) (h : AlgebraTools.FinOrb J J (d : G)) :
    AlgebraTools.FinOrb (J.subgroupOf H) (J.subgroupOf H) d := by
  let f : H ⧸ J.subgroupOf H → G ⧸ J := Quotient.map' (fun x : H => (x : G)) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    exact Subgroup.mem_subgroupOf.1 hab)
  have hf : Function.Injective f := by
    intro a b
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    intro hab
    exact QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (QuotientGroup.eq.1 hab))
  refine Set.Finite.of_finite_image (Set.Finite.subset h ?_) hf.injOn
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  exact ⟨⟨u.1.1, Subgroup.mem_subgroupOf.1 u.2⟩, rfl⟩

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem det_cLoc (x : UA L 2) (u : Plc L) :
    (mL u x).det = pLoc L u (pFin L ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L)).det) := by
  have h : mL u x = ((pLoc L u).comp (pFin L)).mapMatrix ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L)) := rfl
  rw [h, ← RingHom.map_det]
  rfl

private theorem det_places (x : UA L 2) (hx : x ∈ SUA L) (u : Plc L) : (mL u x).det = 1 := by
  have h : ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L)).det = 1 :=
    congrArg Units.val (show Matrix.GeneralLinearGroup.det (x : GL (Fin 2) (Ad L)) = 1 from hx)
  rw [det_cLoc, h, map_one, map_one]

private theorem mem_SUA_of_places (x : UA L 2) (hx : x ∈ finU (E := L) (n := 2)) (h : ∀ u : Plc L, (mL u x).det = 1) : x ∈ SUA L := by
  show Matrix.GeneralLinearGroup.det (x : GL (Fin 2) (Ad L)) = 1
  apply Units.ext
  show ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L)).det = 1
  have hi : (pInf L).mapMatrix ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L)) = 1 :=
    congrArg (fun y : GL (Fin 2) (Cinf L) => (y : Matrix (Fin 2) (Fin 2) (Cinf L))) (show cInf x = 1 from hx)
  apply Prod.ext
  · refine (infEq L).symm.injective ?_
    have := RingHom.map_det (pInf L) ((x : GL (Fin 2) (Ad L)) : Matrix (Fin 2) (Fin 2) (Ad L))
    rw [hi, Matrix.det_one] at this
    exact this.trans (map_one (pInf L)).symm
  · apply Subtype.ext
    funext u
    have := det_cLoc x u
    rw [h u] at this
    exact this.symm.trans rfl

private theorem dc_eq_of_local {G M Gl V : Type} [Group G] [Group M] [Group Gl] [AddCommGroup V] [Module ℂ V]
    (Q : Subgroup M) (e : G ≃* Q) (sec : Gl →* M) (c : M →* Gl) (hcs : ∀ x, c (sec x) = x)
    (hsu : ∀ x ∈ Q, sec (c x) ∈ Q)
    (hcomm : ∀ x ∈ Q, ∀ h, sec h ∈ Q → Commute (sec h) (x * (sec (c x))⁻¹))
    (J₀ : Subgroup Gl) (U₁ U₂ : Subgroup G)
    (h₁ : ∀ u ∈ U₁, c (e u) ∈ J₀) (h₂ : ∀ u ∈ U₂, c (e u) ∈ J₀)
    (h₃ : ∀ u : G, (∃ h ∈ J₀, (e u : M) = sec h) → u ∈ U₁) (h₁₂ : U₁ ≤ U₂)
    (d : Gl) (hd : AlgebraTools.FinOrb J₀ J₀ d) (g : G) (hg : (e g : M) = sec d)
    (ψ : G → V) (hψ : ∀ u ∈ U₂, ∀ x, ψ (x * u) = ψ x) : dcF U₁ g ψ = dcF U₂ g ψ := by
  let Hs : Subgroup Gl := Q.comap sec
  let j : Hs →* G := e.symm.toMonoidHom.comp (sec.subgroupComap Q)
  let p : G →* Hs := MonoidHom.codRestrict (c.comp (Q.subtype.comp e.toMonoidHom)) Hs (fun u => hsu _ (e u).2)
  have hej : ∀ x : Hs, (e (j x) : M) = sec x := fun x => by
    show ((e (e.symm _)) : M) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hp : ∀ u : G, (p u : Gl) = c (e u) := fun _ => rfl
  let J : Subgroup Hs := J₀.subgroupOf Hs
  have hpj : ∀ x, p (j x) = x := fun x => Subtype.ext (by rw [hp, hej, hcs])
  have hcm : ∀ (u : G) (x : Hs), u * (j (p u))⁻¹ * j x = j x * (u * (j (p u))⁻¹) := by
    intro u x
    apply e.injective
    apply Subtype.ext
    have := hcomm _ (e u).2 x x.2
    simp only [map_mul, map_inv, Subgroup.coe_mul, InvMemClass.coe_inv, hej, hp]
    exact this.symm.eq
  have hJ₁ : ∀ h ∈ J, j h ∈ U₁ := fun h hh => h₃ _ ⟨h, Subgroup.mem_subgroupOf.1 hh, hej h⟩
  have hdH : d ∈ Hs := by
    show sec d ∈ Q
    rw [← hg]
    exact (e g).2
  have hgj : g = j ⟨d, hdH⟩ := by
    apply e.injective
    apply Subtype.ext
    rw [hg, hej]
  have hfin : AlgebraTools.FinOrb J J (⟨d, hdH⟩ : Hs) := finOrb_subgroupOf Hs J₀ _ hd
  have k₁ := dcLocal Hs G V j p J U₁ hpj
    (fun u hu => ⟨Subgroup.mem_subgroupOf.2 (h₁ u hu), hcm u⟩) hJ₁ _ hfin
  have k₂ := dcLocal Hs G V j p J U₂ hpj
    (fun u hu => ⟨Subgroup.mem_subgroupOf.2 (h₂ u hu), hcm u⟩) (fun h hh => h₁₂ (hJ₁ h hh)) _ hfin
  rw [hgj, k₁.2 ψ fun u hu => hψ u (h₁₂ hu), k₂.2 ψ hψ]

private theorem sec_cLoc (w : Plc L) (h : IsSplitAt w) (x : UA L 2) (hx : x ∈ finU (E := L) (n := 2)) (u : Plc L) (hu : un u = un w) :
    cLoc u (secW 2 w (cLoc w x)) = cLoc u x := by
  obtain ⟨f1, -, -, -, -, -, f7, -⟩ := uaFacts L 2
  obtain ⟨a, ha, hau⟩ := f7 w x hx
  have e : a = secW 2 w (cLoc w x) := by
    have := (f1 w h).2.2.2 a ha
    rwa [hau w rfl] at this
  rw [← e]
  exact hau u hu

private theorem loc_off (w : Plc L) (x : UA L 2) (hx : x ∈ locU 2 w) (u : Plc L) (hu : un u ≠ un w) : cLoc u x = 1 :=
  Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) hu

private theorem sec_mem (w : Plc L) (h : IsSplitAt w) (x : UA L 2) (hx : x ∈ finU (E := L) (n := 2) ⊓ SUA L) :
    secW 2 w (cLoc w x) ∈ finU (E := L) (n := 2) ⊓ SUA L := by
  have hl : secW 2 w (cLoc w x) ∈ locU 2 w := ((uaFacts L 2).1 w h).1 _
  have hf : secW 2 w (cLoc w x) ∈ finU (E := L) (n := 2) := (Subgroup.mem_inf.1 hl).1
  refine Subgroup.mem_inf.2 ⟨hf, mem_SUA_of_places _ hf fun u => ?_⟩
  by_cases hu : un u = un w
  · have := det_places x (Subgroup.mem_inf.1 hx).2 u
    rwa [mL, ← sec_cLoc w h x (Subgroup.mem_inf.1 hx).1 u hu] at this
  · rw [mL, loc_off w _ hl u hu]
    simp

private theorem sec_comm (w : Plc L) (h : IsSplitAt w) (x : UA L 2) (hx : x ∈ finU (E := L) (n := 2)) (a : GL (Fin 2) (Kw w)) :
    Commute (secW 2 w a) (x * (secW 2 w (cLoc w x))⁻¹) := by
  refine (uaFacts L 2).2.1 w _ (((uaFacts L 2).1 w h).1 a) _ fun u hu => ?_
  rw [map_mul, map_inv, sec_cLoc w h x hx u hu, mul_inv_cancel]

private theorem eD_congr {K : Type} [Field K] {Δ s s' : K} (a : s * s = Δ) (b : s' * s' = Δ) (h : s = s') : eD a = eD b := by
  subst h; rfl

private theorem iw_KGL (R : RingBr L) (w : Plc L) (Sp : R.Split w) (a : GL (Fin 2) (Kw w)) (ha : a ∈ (iw w).J 2) :
    a ∈ GlobalTheory.LFun.KGL w (n := 2) := by
  let g₀ : GL (Fin 2) (Kv (un w)) := Matrix.GeneralLinearGroup.map (Sp.i.symm : Kw w →+* Kv (un w)) a
  have e : Matrix.GeneralLinearGroup.map (Sp.i : Kv (un w) →+* Kw w) g₀ = a := by
    ext i j
    simp [g₀]
  rw [← e] at ha ⊢
  exact (Sp.K 2 g₀).2 (((finFacts _ (Lev.iw _)).2.2.2.2.2 2).2.2.2 ((Sp.J (Lev.iw _) (iw w) rfl Sp.Uo 2 g₀).1 ha))

private theorem sec_lev (R : RingBr L) (w : Plc L) (h : IsSplitAt w) (Sp : R.Split w) (U : Subgroup (UA L 2)) (hU : Full U {w})
    (S₁ : Finset (Plc L)) (hS : ∀ w' ∈ S₁, w' ≠ w → un w' ≠ un w) (a : GL (Fin 2) (Kw w)) (ha : a ∈ (iw w).J 2) :
    secW 2 w a ∈ lev U S₁ iw := by
  have hl : secW 2 w a ∈ locU 2 w := ((uaFacts L 2).1 w h).1 a
  have hc : cLoc w (secW 2 w a) = a := ((uaFacts L 2).1 w h).2.1 a
  have hK : secW 2 w a ∈ Kall L 2 := by
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hl).1, Subgroup.mem_iInf.2 fun u => ?_⟩
    show cLoc u (secW 2 w a) ∈ GlobalTheory.LFun.KGL u (n := 2)
    by_cases hu : un u = un w
    · exact (uaFacts L 2).2.2.2.2.2.2.2 w h _ (by rw [hc]; exact iw_KGL R w Sp a ha) u hu
    · rw [loc_off w _ hl u hu]
      exact one_mem _
  refine Subgroup.mem_inf.2 ⟨hU.2 w (Finset.mem_singleton_self w) (Subgroup.mem_inf.2 ⟨hl, hK⟩), ?_⟩
  refine Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun hw' => ?_
  show cLoc w' (secW 2 w a) ∈ (iw w').J 2
  by_cases e : w' = w
  · subst e
    rwa [hc]
  · rw [loc_off w _ hl w' (hS w' hw' e)]
    exact one_mem _

private theorem lvS_loc (B : Bridge L) (hB : B.Ok) (T : Spl B) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ) (hA : A.Ok)
    (hF : Fit T S VL A) (w : Plc L) (hw : w ∈ S) (h : IsSplitAt w) (hiw : VL w = iw w) (y : DA B.Δ) (hy : A.dat.Off y)
    (u : SA B.Δ) (hu : u ∈ A.lvS y) : cLoc w (B.bS u : UA L 2) ∈ (iw w).J 2 := by
  have hv : un w ∈ A.Sg := (hF.sg _).2 ⟨w, hw, rfl⟩
  have h1 : y⁻¹ * (u : DA B.Δ) * y⁻¹⁻¹ ∈ A.dat.U2 := Subgroup.mem_subgroupOf.1 hu
  have h2 := (((datOk _ _ A hA).2.2.2.2 _).1 h1).1 (un w) hv
  have h3 : (y⁻¹ * (u : DA B.Δ) * y⁻¹⁻¹).1 (un w) = (u : DA B.Δ).1 (un w) := by
    show (y.1 (un w))⁻¹ * (u : DA B.Δ).1 (un w) * ((y.1 (un w))⁻¹)⁻¹ = _
    rw [hy _ hv]
    simp
  rw [h3, eD_congr (A.hs _ hv) (T w h).hs (hF.s w hw h)] at h2
  rw [hB.splS w (T w h) u, ← hiw]
  exact ((T w h).J (A.V (un w)) (VL w) (hF.c w hw) (hF.H w hw h) 2 _).2 h2

end UpperTheory.V.Z.Sym.So

namespace UpperTheory.V.Z.Sym.So

private theorem genL {F : Type} [Field F] [NumberField F] {Δ : F} (A : SD Δ) (y : DA Δ) {M Gl V : Type} [Group M] [Group Gl] [AddCommGroup V] [Module ℂ V]
    (Q : Subgroup M) (e : SA Δ ≃* Q) (sec : Gl →* M) (c : M →* Gl) (hcs : ∀ x, c (sec x) = x)
    (hsu : ∀ x ∈ Q, sec (c x) ∈ Q) (hcomm : ∀ x ∈ Q, ∀ h, sec h ∈ Q → Commute (sec h) (x * (sec (c x))⁻¹))
    (J₀ : Subgroup Gl) (U : Subgroup M) (h₁ : ∀ u ∈ U, c u ∈ J₀) (h₂ : ∀ u : SA Δ, u ∈ A.lvS y → c (e u) ∈ J₀)
    (h₃ : ∀ h ∈ J₀, sec h ∈ U) (h₁₂ : ∀ u : SA Δ, (e u : M) ∈ U → u ∈ A.lvS y)
    (d : Gl) (hd : AlgebraTools.FinOrb J₀ J₀ d) (g : SA Δ) (hg : (e g : M) = sec d)
    (ψ : SA Δ → V) (hψ : ∀ u ∈ A.lvS y, ∀ x, ψ (x * u) = ψ x) :
    dcF ((U.subgroupOf Q).comap e.toMonoidHom) g ψ = dcF (A.lvS y) g ψ :=
  dc_eq_of_local Q e sec c hcs hsu hcomm J₀ _ _ (fun _ hu => h₁ _ hu) h₂
    (fun u hu => hu.elim fun h hh => show (e u : M) ∈ U from hh.2 ▸ h₃ h hh.1) (fun u hu => h₁₂ u hu) d hd g hg ψ hψ

private theorem sLev0 {L : Type} [Field L] [NumberField L] [IsCMField L] (B : Bridge L) (hB : B.Ok) (T : Spl B) (S : Finset (Plc L))
    (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ) (hA : A.Ok) (hF : Fit T S VL A) (w : Plc L) (hwS : w ∈ S) (h : IsSplitAt w)
    (S₁ : Finset (Plc L)) (hwS₁ : w ∈ S₁) (hS₁ : S₁ ⊆ S) (hiw : VL w = iw w) (U : Subgroup (UA L 2)) (hU : Full U {w})
    (y : DA B.Δ) (hy : A.dat.Off y) (hlev : ∀ g : SA B.Δ, (B.bS g : UA L 2) ∈ lev U S₁ iw → g ∈ A.lvS y)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ψ : SA B.Δ → V) (hψ : ∀ u ∈ A.lvS y, ∀ g, ψ (g * u) = ψ g) (g : SA B.Δ)
    (d : Fin 2 → (Kw w)ˣ) (hg : (B.bS g : UA L 2) = secW 2 w (Sig.dg d)) :
    dcF (((lev U S₁ iw).subgroupOf (finU (E := L) (n := 2) ⊓ SUA L)).comap B.bS.toMonoidHom) g ψ = dcF (A.lvS y) g ψ :=
  genL A y (finU (E := L) (n := 2) ⊓ SUA L) B.bS (secW 2 w) (cLoc w) ((uaFacts L 2).1 w h).2.1 (sec_mem w h)
    (fun x hx a _ => sec_comm w h x hx.1 a) ((iw w).J 2) (lev U S₁ iw)
    (fun _ hu => Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hu.2 w) hwS₁)
    (lvS_loc B hB T S VL A hA hF w hwS h hiw y hy)
    (sec_lev B.toRingBr w h (T w h) U hU S₁ fun _ hw' e e' => e (hF.pl.inj (Finset.mem_coe.2 (hS₁ hw')) (Finset.mem_coe.2 hwS) e'))
    hlev (Sig.dg d) (((finFacts _ (iw w)).2.2.2.2.2 2).1 _) g hg ψ hψ

end UpperTheory.V.Z.Sym.So

set_option allowUnsafeReducibility true in
attribute [local irreducible] cv Kv Ov DX KD RP SA Lsq dcF SD.lvS lev SUA Subgroup.comap MulEquiv.toMonoidHom Subgroup.toGroup Subgroup.subgroupOf

theorem UpperTheory.V.Z.Sym.So.sLev :
    UpperTheory.V.Z.Sym.So.SLev := by
  intro L _ _ _ B hB T S VL A hA hF w hw h S₁ a b c U hU y hy hl V _ _ ψ hψ g d hg
  have k := sLev0 B hB T S VL A hA hF w hw h S₁ a b c U hU y hy hl V ψ hψ g d hg
  exact k

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.FinToAF
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem core {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (Fi In Rt U : Subgroup G) [hN : Fi.Normal] (c : G →* H) (R : Representation ℂ H V)
    (hdec : ∀ x : G, ∃ f ∈ Fi, ∃ k ∈ In, x = f * k)
    (hcomm : ∀ f ∈ Fi, ∀ k ∈ In, Commute f k)
    (hint : ∀ x ∈ Fi, x ∈ In → x = 1)
    (hc : ∀ x ∈ Fi, c x = 1)
    (hU : U ≤ Fi)
    (Φ : Fi → V)
    (hL : ∀ (f : Fi), ∀ k ∈ In, (f : G) * k ∈ Rt → ∀ g, Φ (f * g) = R (c k) (Φ g))
    (hV : ∀ u : Fi, (u : G) ∈ U → ∀ g, Φ (g * u) = Φ g) :
    ∃ φ : G → V, (∀ γ ∈ Rt, ∀ g, φ (γ * g) = φ g) ∧ (∀ x ∈ In, ∀ g, φ (g * x) = R (c x⁻¹) (φ g)) ∧
      (∀ u ∈ U, ∀ g, φ (g * u) = φ g) ∧ (∀ g : Fi, φ g = Φ g) ∧
      ∀ (x : Fi) (cc : ℂ), UpperTheory.V.AlgebraTools.FinOrb U U (x : G) →
        dcF (U.subgroupOf Fi) x Φ = cc • Φ → dcF U (x : G) φ = cc • φ := by
  classical
  have hex : ∀ x : G, ∃ f : Fi, (f : G)⁻¹ * x ∈ In := by
    intro x
    obtain ⟨f, hf, k, hk, rfl⟩ := hdec x
    exact ⟨⟨f, hf⟩, by simpa using hk⟩
  choose p hp using hex
  have hpu : ∀ (f : Fi) (k : G), k ∈ In → p ((f : G) * k) = f := by
    intro f k hk
    have h2 : ((p ((f : G) * k) : G)⁻¹ * f) ∈ In := by
      have := In.mul_mem (hp ((f : G) * k)) (In.inv_mem hk)
      simpa [mul_assoc] using this
    have h3 : ((p ((f : G) * k) : G)⁻¹ * f) ∈ Fi := Fi.mul_mem (Fi.inv_mem (p _).2) f.2
    exact Subtype.ext (inv_mul_eq_one.mp (hint _ h3 h2))
  have hfac : ∀ g : G, ∃ k ∈ In, g = (p g : G) * k := fun g => ⟨_, hp g, by simp⟩
  have hmulR : ∀ (g : G) (f : Fi), p (g * f) = p g * f := by
    intro g f
    obtain ⟨k, hk, hg⟩ := hfac g
    have : g * f = ((p g * f : Fi) : G) * k := by
      have h := (hcomm f f.2 k hk).eq
      calc g * f = (p g : G) * (k * f) := by rw [← mul_assoc, ← hg]
        _ = _ := by rw [← h]; simp [mul_assoc]
    rw [this, hpu _ _ hk]
  have hmulL : ∀ (f : Fi) (g : G), p ((f : G) * g) = f * p g := by
    intro f g
    obtain ⟨k, hk, hg⟩ := hfac g
    have : (f : G) * g = ((f * p g : Fi) : G) * k := by
      calc (f : G) * g = (f : G) * ((p g : G) * k) := by rw [← hg]
        _ = _ := by simp [mul_assoc]
    rw [this, hpu _ _ hk]
  have hmulIn : ∀ (g k : G), k ∈ In → p (g * k) = p g := by
    intro g k hk
    obtain ⟨k', hk', hg⟩ := hfac g
    have : g * k = (p g : G) * (k' * k) := by
      calc g * k = (p g : G) * k' * k := by rw [← hg]
        _ = _ := by rw [mul_assoc]
    rw [this, hpu _ _ (In.mul_mem hk' hk)]
  have hinL : ∀ (k g : G), k ∈ In → p (k * g) = p g := by
    intro k g hk
    obtain ⟨k', hk', hg⟩ := hfac g
    have : k * g = (p g : G) * (k * k') := by
      have h := (hcomm (p g) (p g).2 k hk).eq
      calc k * g = k * ((p g : G) * k') := by rw [← hg]
        _ = _ := by rw [← mul_assoc, ← h, mul_assoc]
    rw [this, hpu _ _ (In.mul_mem hk hk')]
  refine ⟨fun x => R (c x)⁻¹ (Φ (p x)), ?_, ?_, ?_, ?_, ?_⟩
  · intro γ hγ g
    have hk := hp γ
    have hγ' : (p γ : G) * ((p γ : G)⁻¹ * γ) = γ := by simp
    have hcγ : c ((p γ : G)⁻¹ * γ) = c γ := by
      rw [map_mul, map_inv, hc _ (p γ).2]; simp
    have hpp : p (γ * g) = p γ * p g := by
      have : γ * g = (p γ : G) * (((p γ : G)⁻¹ * γ) * g) := by simp [mul_assoc]
      rw [this, hmulL, hinL _ _ hk]
    have h := hL (p γ) _ hk (by rw [hγ']; exact hγ) (p g)
    simp only [hpp, h, hcγ, map_mul, mul_inv_rev, Module.End.mul_apply]
    rw [← Module.End.mul_apply (R (c γ)⁻¹), ← map_mul]
    simp
  · intro x hx g
    simp only [hmulIn g x hx, map_mul, mul_inv_rev, map_inv, Module.End.mul_apply]
  · intro u hu g
    have h := hmulR g ⟨u, hU hu⟩
    simp only at h
    simp only [h, map_mul, hc u (hU hu), mul_one]
    rw [hV ⟨u, hU hu⟩ hu]
  · intro g
    have h := hpu g 1 In.one_mem
    rw [mul_one] at h
    simp [h, hc _ g.2]
  · intro x cc hfo heig
    obtain ⟨hfo', hDC, -, Rr, hR1, hR2, hR3⟩ := dcSub G V Fi U x hfo
      (fun u hu => ⟨1, U.one_mem, by simp, by simpa using hU hu, by simpa using hU hu⟩) hN
    have hΦ : ∀ u ∈ U.subgroupOf Fi, ∀ g, Φ (g * u) = Φ g := fun u hu g => hV u hu g
    have hsum := (dcBasic Fi V (U.subgroupOf Fi) x hfo' Φ hΦ).2.2.2.2 Rr hR1 hR2
    have hφ : ∀ u ∈ U, ∀ g, (fun x => R (c x)⁻¹ (Φ (p x))) (g * u) = (fun x => R (c x)⁻¹ (Φ (p x))) g := by
      intro u hu g
      have h := hmulR g ⟨u, hU hu⟩
      simp only at h
      simp only [h, map_mul, hc u (hU hu), mul_one]
      rw [hV ⟨u, hU hu⟩ hu]
    have hsum' := (dcBasic G V U x hfo (fun x => R (c x)⁻¹ (Φ (p x))) hφ).2.2.2.2 (Rr.map (Function.Embedding.subtype _))
      (by
        intro y hy
        obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp hy
        exact (hDC r).1 (hR1 r hr))
      (by
        intro y hy
        obtain ⟨r, ⟨hr, hry⟩, hu⟩ := hR3 y hy
        refine ⟨r, ⟨Finset.mem_map.mpr ⟨r, hr, rfl⟩, hry⟩, ?_⟩
        rintro r' ⟨hr', hry'⟩
        obtain ⟨r'', hr'', rfl⟩ := Finset.mem_map.mp hr'
        simpa using congrArg Subtype.val (hu r'' ⟨hr'', hry'⟩))
    funext g
    rw [hsum' g, Finset.sum_map]
    have hE := congrFun heig (p g)
    rw [hsum (p g)] at hE
    simp only [Function.Embedding.subtype_apply, Pi.smul_apply]
    have : ∀ r : Fi, R (c (g * r))⁻¹ (Φ (p (g * r))) = R (c g)⁻¹ (Φ (p g * r)) := by
      intro r
      rw [hmulR, map_mul, hc _ r.2, mul_one]
    simp only [this]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, hE, Pi.smul_apply, map_smul]

theorem UpperTheory.V.Z.Sym.So.finToAF :
    UpperTheory.V.Z.Sym.So.FinToAF := by
  intro L _ _ _ n V _ _ R U hU Φ hL hV
  obtain ⟨-, -, hdec, hcomm, hext, hmem, -, -⟩ := uaFacts L n
  have hN : (finU (E := L) (n := n)).Normal := ⟨fun x hx g => (hmem _).1.2 fun τ => by
    simp [((hmem x).1.1 hx) τ]⟩
  obtain ⟨φ, h1, h2, h3, h4, h5⟩ := core (finU (E := L) (n := n)) (infU L n) (ratU L n) U (infC L n) R hdec hcomm
    (fun x hx hx' => hext x 1 (fun w => by simpa using (hmem x).2.1 hx' w)
      (fun τ => by simpa using (hmem x).1.1 hx τ))
    (fun x hx => by
      funext v
      exact (hmem x).1.1 hx v.embedding)
    hU Φ hL hV
  exact ⟨φ, ⟨h1, h2, h3⟩, h4, h5⟩

end
end

