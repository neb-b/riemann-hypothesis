module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNFact
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem cong_conj_iff (hG : CongGrpEx) {E : Type} [Field E] [NumberField E] [IsCMField E] (n N : ℕ) (hN : 0 < N)
    (u : Plc E) (a : GLw n u) (ha : a ∈ GlobalTheory.LFun.KGL u (n := n)) (y : GLw n u) :
    (Cong1 N u (a * y * a⁻¹) ∧ Cong1 N u (a * y * a⁻¹)⁻¹) ↔ Cong1 N u y ∧ Cong1 N u y⁻¹ := by
  obtain ⟨K, hc, -, -, -, hn, -, -⟩ := hG E n N hN u
  rw [← hc, ← hc]
  exact hn a ha y

private theorem principalCongruence_one {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (N : ℕ) (u : Plc E) :
    Cong1 N u (1 : GLw n u) := by
  intro i k
  simp

theorem UpperTheory.Gal.W2.Seed.pKNFact :
    KNIff → FacEq → AtApart → CongGrpEx → CongConj → UpperTheory.Gal.W2.Seed.LocComm → UpperTheory.Gal.CertificateRingHomMap.LocComm → KNFact := by
  intro hK _ _ hG hC _ hL E _ _ _ A n p _ S F w L hF q hq hgood hqw N hN K hKc
  have e : ∀ (u : Plc E) (g : GUf E n), GeneralLinearGroup.map (pLoc E u) (F.tr.a * mat g * F.tr.a⁻¹) =
      F.a u * comp u g * (F.a u)⁻¹ := by
    intro u g
    rw [F.a_tr]
    simp only [map_mul, map_inv]
    rfl
  have hCong : ∀ g : GUf E n, S.L.CongOne N (F.j g) ↔ ∀ u : Plc E, (p : 𝓞 E) ∉ u.asIdeal →
      Cong1 N u (F.a u * comp u g * (F.a u)⁻¹) := by
    intro g
    rw [F.j_tr, ((hK E A n p S F.tr g).2 N hN)]
    simp only [e]
  have einv : ∀ (u : Plc E) (g : GUf E n), F.a u * comp u g⁻¹ * (F.a u)⁻¹ = (F.a u * comp u g * (F.a u)⁻¹)⁻¹ := by
    intro u g
    rw [map_inv]
    group
  have hw := (hL E n w.1 w.2.1)
  have hcs : IsSplitAt (CertificateRingHomMap.cj w.1) := hw.2.2.2.1
  have hqc : (q : 𝓞 E) ∈ (CertificateRingHomMap.cj w.1).asIdeal := by
    by_contra hc
    haveI : Fact q.Prime := ⟨hq⟩
    have h1 : GlobalTheory.Cong.Apart w.1 (CertificateRingHomMap.cj w.1) := apart_of_not_mem (p := q) hc hqw
    exact (((hL E n (CertificateRingHomMap.cj w.1) hcs).2.1 w.1).1 h1).2 hw.2.2.2.2.1.symm
  have hcw := F.a_int w.1 q hq hgood hqw
  have hcc := F.a_int _ q hq hgood hqc
  have main : ∀ y : GLw n w.1, Cong1 N w.1 y → Cong1 N w.1 y⁻¹ → S.L.CongOne N (L.loc y) := by
    intro y h1 h2
    rw [hF.2, hCong]
    intro u _
    by_cases huw : u = w.1
    · subst huw
      rw [CertificateRingHomMap.comp_loc]
      exact ((cong_conj_iff hG n N hN _ _ hcw y).2 ⟨h1, h2⟩).1
    by_cases huc : u = CertificateRingHomMap.cj w.1
    · subst huc
      have c1 : Cong1 N (CertificateRingHomMap.cj w.1) (comp (CertificateRingHomMap.cj w.1) (CertificateRingHomMap.loc w.2.1 y)) :=
        hC E n N w.1 _ (CertificateRingHomMap.sim_loc _ _) (by rwa [CertificateRingHomMap.comp_loc])
      have c2 : Cong1 N (CertificateRingHomMap.cj w.1) (comp (CertificateRingHomMap.cj w.1) (CertificateRingHomMap.loc w.2.1 y))⁻¹ := by
        rw [← map_inv]
        exact hC E n N w.1 _ (by rw [map_inv, CertificateRingHomMap.sim_loc, inv_one]) (by rwa [map_inv, CertificateRingHomMap.comp_loc, inv_inv])
      exact ((cong_conj_iff hG n N hN _ _ hcc _).2 ⟨c1, c2⟩).1
    · rw [CertificateRingHomMap.comp_loc_of_apart w.2.1 (((hw.2.1 u).2 ⟨huw, huc⟩)) y]
      simpa using principalCongruence_one N u
  refine ⟨fun y hy => ?_, fun k hk => ?_⟩
  · obtain ⟨h1, h2⟩ := (hKc y).1 hy
    refine ⟨main y h1 h2, ?_⟩
    rw [← map_inv]
    exact main y⁻¹ h2 (by rwa [inv_inv])
  · obtain ⟨g, rfl⟩ := F.surj k
    rw [hF.1, hKc]
    have h1 := (hCong g).1 hk.1 w.1 w.2.2
    have h2 := (hCong g⁻¹).1 (by rw [map_inv]; exact hk.2) w.1 w.2.2
    rw [einv] at h2
    exact (cong_conj_iff hG n N hN _ _ hcw _).1 ⟨h1, h2⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLevSec
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pLevSec :
    UpperTheory.Gal.W2.Seed.IntConj → LevSec := by
  intro hIC E _ _ _ A n p _ S T S₀ Kw hS
  have hn : 0 < n := S.facts.pos
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 E)
  let w₀ : Plc E := ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩
  have hsim : ∀ g : GUf E n, (∀ u, comp u g ∈ GlobalTheory.LFun.KGL u (n := n)) → sim g ∈ UpperTheory.Gal.CertificateRingHomMap.ZU :=
    fun g h => (hIC E n g w₀ hn).2.1 h
  have hcj : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → (p : 𝓞 E) ∈ (UpperTheory.Gal.CertificateRingHomMap.cj w).asIdeal := by
    intro w hw
    have h1 : (p : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      show algebraMap _ (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal
      simpa using hw
    rw [← GlobalTheory.LocInj.under_conjSrc w] at h1
    have h2 : algebraMap _ (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ (UpperTheory.Gal.CertificateRingHomMap.cj w).asIdeal := h1
    simpa using h2
  refine ⟨fun k hk => ?_, fun k h1 h2 _ => ?_⟩
  · obtain ⟨hs, hK, hR⟩ := UpperTheory.Gal.CertificateRingHomMap.mem_lev.1 hk
    have hoff : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w (T.sec (T.j k)) = comp w k :=
      (T.j_eq _ _).1 (T.j_sec _)
    have hover : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k ∈ GlobalTheory.LFun.KGL w (n := n) := fun w hw =>
      hR w (fun h => hS w h hw) (fun h => hS _ h (hcj w hw))
    have hq : sim ((T.sec (T.j k))⁻¹ * k) ∈ UpperTheory.Gal.CertificateRingHomMap.ZU := by
      refine hsim _ fun u => ?_
      rw [map_mul, map_inv]
      by_cases hu : (p : 𝓞 E) ∈ u.asIdeal
      · rw [T.sec_p _ u hu, inv_one, one_mul]
        exact hover u hu
      · rw [hoff u hu, inv_mul_cancel]
        exact one_mem _
    refine UpperTheory.Gal.CertificateRingHomMap.mem_lev.2 ⟨?_, fun w hw => ?_, fun w hw hcw => ?_⟩
    · have e : sim (T.sec (T.j k)) = sim k * (sim ((T.sec (T.j k))⁻¹ * k))⁻¹ := by
        rw [map_mul, map_inv]; simp
      rw [e]
      exact mul_mem hs (inv_mem hq)
    · rw [hoff w (hS w hw)]
      exact hK w hw
    · by_cases hu : (p : 𝓞 E) ∈ w.asIdeal
      · rw [T.sec_p _ w hu]
        exact one_mem _
      · rw [hoff w hu]
        exact hR w hw hcw
  · have hall : ∀ u, comp u k ∈ GlobalTheory.LFun.KGL u (n := n) := fun u => by
      by_cases hu : (p : 𝓞 E) ∈ u.asIdeal
      · exact h2 u hu
      · rw [h1 u hu]; exact one_mem _
    refine UpperTheory.Gal.CertificateRingHomMap.mem_lev.2 ⟨hsim k hall, fun w hw => ?_, fun w _ _ => hall w⟩
    rw [h1 w (hS w hw)]
    exact one_mem _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PMemFn
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pMemFn :
    SeenShape → SeenActs → ActsConv → TyFact → MemFn := by
  intro hSh hAc hAC hTF E _ _ _ A n p _ S F x U w₀ Up V h1 h2 h3 h4 h5 r W hAux N hrN hSt L hw Ty hTy g θ hs
  obtain ⟨-, hcase⟩ := hSh E A n p S F x U w₀ Up V h1 h2 h3 h4 h5 r W hAux N hrN hSt L hw Ty hTy g θ hs
  obtain ⟨hsupp, hdeck, hgen⟩ := hAc E A n p S F x U w₀ Up V h1 h2 h3 h4 h5 r W hAux N hrN hSt L hw Ty hTy g θ hs
  obtain ⟨tf1, tf2, -⟩ := hTF E A n p S F x U w₀ Up V h1 h2 h3 h4 h5 r W hAux N hrN hSt L hw Ty hTy
  rcases hcase with ⟨hD, hh, hθ⟩ | ⟨w, t, z, i, B, hFree, hAp, -, -, -, -, -, hinv, hCen, hWpr, hFg, -⟩
  · have hA := hdeck hD hh
    have hhK : g.h ∈ Ty.K := ((Ty.mem_kerK _).1 hh).1
    refine ⟨hA.1, ?_, Or.inl ⟨hD, hθ, ?_⟩⟩
    · intro a ha u hu
      obtain ⟨k, hk, hka⟩ := hsupp a ha
      have haK : a ∈ Ty.K := by
        have e : a = (g.h * k)⁻¹ * (g.h * k * a) := by group
        rw [e]
        exact Ty.K.mul_mem (Ty.K.inv_mem (Ty.K.mul_mem hhK hk)) hka
      exact (tf1 u hu).1.2 a haK
    · have e := (hAC _ _ Ty _ _ _ hA).1
      rwa [one_smul] at e
  · obtain ⟨hfac, hap⟩ := tf2 w hFree.2.1 hFree.2.2.1 hAp
    have hA := hgen _ (L w) _ t⁻¹ (F.j (z ^ i)⁻¹) hfac hFg hap hCen hinv
    have hpr : Ty.L.pr g.h = 1 := by
      have e := hA.2.1
      rwa [map_inv, inv_eq_one] at e
    refine ⟨hA.1, ?_, Or.inr ⟨hpr, hWpr, (hAC _ _ Ty _ _ _ hA).1⟩⟩
    intro a ha u hu
    obtain ⟨k, hk, hka⟩ := hsupp a ha
    have f := (tf1 u hu).1.2
    have e : (L u).pr (g.h * k * a) = (L u).pr k * (L u).pr a := by
      rw [map_mul, map_mul, hWpr u hu, one_mul]
    have h6 := f _ hka
    rw [e] at h6
    exact (Subgroup.mul_mem_cancel_left _ (f k hk)).1 h6
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPhiEx
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pPhiEx :
    PhiTy → SeenShape → SeenActs → TyFact → TfAct → TfCen → TEig → AtApart → FacEq → JEq → UpperTheory.Gal.W2.Seed.LocComm → PhiEx := by
  intro hTy hShape hActs hFact hTfAct hTfCen hTEig hAt hFac hJ hc E _ _ _ A n p _ S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok
  obtain ⟨h0, h1, h2, -⟩ := hTy E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok
  refine ⟨fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h)), h0, h1, ?_, ?_⟩
  · intro g hg
    have := h2 g hg
    rw [th_eq F]
    exact this
  · intro g θ hs
    obtain ⟨-, hcase⟩ := hShape E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok g θ hs
    have hA := hActs E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok g θ hs
    rcases hcase with ⟨hd, hk, rfl⟩ | ⟨w, t, z, i, B, hfree, hap, hi, hT, hz, hB, hzp, hh, hcen, -, hLf, rfl⟩
    · have h3 := (hA.2.1 hd hk).2.2 _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1
      rw [h3]
      funext a
      have h4 := hTfCen _ _ Ty 1 ⟨fun _ => by simp, map_one _⟩ _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1 a
      simp only [Pi.smul_apply, one_smul]
      rw [h4, mul_one]
    · obtain ⟨hLK, hLA⟩ := (hFact E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok).2.1 w
        hfree.2.1 hfree.2.2.1 hap
      have hAc := hA.2.2 _ (L w) _ t⁻¹ (F.j (z ^ i)⁻¹) hLK hLf hLA hcen hh
      have h3 := hAc.2.2 _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1
      have hsz : F.tr.sec (F.j (z ^ i)⁻¹) = (z ^ i)⁻¹ := by
        apply (hJ E A n p S F.tr.toAdT F.tr.μ F.tr.mu F.tr.a F.tr.j F.tr.j_mx).1
        intro u
        by_cases hu : (p : 𝓞 E) ∈ u.asIdeal
        · rw [F.tr.sec_p _ u hu]
          simp [hzp u hu]
        · exact (F.tr.j_eq _ _).1 (by rw [F.tr.j_sec, F.j_tr]) u hu
      have hsl : ∀ y, F.tr.sec ((L w).loc y) = CertificateRingHomMap.loc w.2.1 y := by
        intro y
        have hL : L w = fac F.tr hc w := (hFac E A n p S F hc w).2 _ (hok.fac w)
        rw [hL]
        exact (hAt E A n p S F.tr hc w.1 w.2.1 w.2.2).1 y
      rw [h3, hh]
      funext a
      have h4 := hTfAct _ _ _ Ty (L w) _ hLK hLA t⁻¹ (F.j (z ^ i)⁻¹) hcen _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1 a
      have h5 := hTEig E n hodd.pos x U w₀ Up V w.1 w.2.1 hfree i hi t hT z hz B hB (F.tr.sec a)
      simp only [Pi.smul_apply]
      rw [h4, mul_smul, ← h5]
      congr 1
      refine finsum_congr fun y => ?_
      simp only [map_mul, hsz, hsl]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPhiTy
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pPhiTy :
    PPart → LevSec → FacEq → UpperTheory.Gal.W2.Seed.LocComm → PhiTy := by
  intro hP hL hF hc E _ _ _ A n p _ S F x U w₀ Up V _ _ _ hOff _ r W hAux N hN hStab L hw Ty hTy
  have hj : F.j = F.tr.j := F.j_tr
  have h4 : ∀ k : GUf E n, (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w k = 1) →
      (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k ∈ GlobalTheory.LFun.KGL w (n := n)) →
      ∀ g, V.Φ (CertificateRingHomMap.th (g * k)) = V.Φ (CertificateRingHomMap.th g) := by
    intro k h1 h2 g
    have hk : CertificateRingHomMap.th k ∈ lev V.S V.Kw :=
      (hL E A n p S F.tr V.S V.Kw hOff.1).2 _
        (fun w hw' => by rw [CertificateRingHomMap.comp_th, h1 w hw', map_one])
        (fun w hw' => by rw [CertificateRingHomMap.comp_th]; exact CertificateRingHomMap.invT_mem_KGL (h2 w hw'))
        (fun u _ => one_mem _)
    have e : comp w₀ (CertificateRingHomMap.th k) = 1 := by rw [CertificateRingHomMap.comp_th, h1 _ hw.2, map_one]
    have hJ : comp w₀ (CertificateRingHomMap.th k) ∈ V.J := e ▸ one_mem _
    have hχ : V.χ ⟨comp w₀ (CertificateRingHomMap.th k), hJ⟩ = 1 := by
      have : (⟨comp w₀ (CertificateRingHomMap.th k), hJ⟩ : V.J) = 1 := Subtype.ext e
      rw [this, map_one]
    rw [map_mul, V.form.right _ hk hJ, hχ]
    simp
  have h3 : ∀ g : GUf E n, (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w g ∈ GlobalTheory.LFun.KGL w (n := n)) →
      V.Φ (CertificateRingHomMap.th (F.tr.sec (F.j g))) = V.Φ (CertificateRingHomMap.th g) := by
    intro g hg
    obtain ⟨k, e, k1, k2, -⟩ := hP E A n p S F.tr g
    have := h4 k k1 (fun w hw' => by rw [k2 w hw']; exact hg w hw') (F.tr.sec (F.tr.j g))
    rw [← e] at this
    rw [hj]
    exact this.symm
  refine ⟨?_, ?_, h3, h4⟩
  · obtain ⟨g₀, h0, hg⟩ := hOff.2
    intro hz
    apply h0
    have e := congrFun hz (F.j (CertificateRingHomMap.th g₀))
    have e' : V.Φ (CertificateRingHomMap.th (F.tr.sec (F.j (CertificateRingHomMap.th g₀)))) = 0 := e
    rw [h3 _ (fun w hw' => by rw [CertificateRingHomMap.comp_th]; exact CertificateRingHomMap.invT_mem_KGL (hg w hw')), CertificateRingHomMap.th_th] at e'
    exact e'
  · intro k hk g
    obtain ⟨⟨k', e, hk'⟩, -⟩ := (hTy.K_iff k).1 hk
    rw [th_eq] at hk'
    have hs : F.tr.sec k ∈ lev V.S (CertificateRingHomMap.levT V.Kw) := by
      have := (hL E A n p S F.tr V.S (CertificateRingHomMap.levT V.Kw) hOff.1).1 k' (CertificateRingHomMap.th_mem_lev.1 hk')
      rwa [← hj, e] at this
    have hs' := CertificateRingHomMap.th_mem_lev.2 hs
    have hpr : Ty.L.pr k = comp w₀ (F.tr.sec k) := by
      have h := (hF E A n p S F hc ⟨w₀, hw⟩).2 _ (hTy.fac ⟨w₀, hw⟩)
      rw [hTy.L_eq, h]
      rfl
    have hyy : (comp w₀ (CertificateRingHomMap.th (F.tr.sec k))).val = ((Ty.L.pr k)⁻¹).valᵀ := by
      rw [CertificateRingHomMap.comp_th, CertificateRingHomMap.invT_val, hpr]
    have hyJ : Ty.L.pr k ∈ Ty.J := Ty.fact.2 k hk
    have hJ' : comp w₀ (CertificateRingHomMap.th (F.tr.sec k)) ∈ V.J := (hTy.J_iff _ _ hyy).1 hyJ
    show V.Φ (CertificateRingHomMap.th (F.tr.sec (g * k))) = ((Ty.ψ ⟨Ty.L.pr k, Ty.fact.2 k hk⟩ : ℂˣ) : ℂ) • V.Φ (CertificateRingHomMap.th (F.tr.sec g))
    rw [map_mul, map_mul, V.form.right _ hs' hJ', hTy.ψ_eq ⟨_, hyJ⟩ ⟨_, hJ'⟩ hyy]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSeenShape
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem seenShape_not_both {E : Type} [Field E] [NumberField E] {u : Plc E} {a b : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hne : a ≠ b) (h1 : (a : 𝓞 E) ∈ u.asIdeal) (h2 : (b : 𝓞 E) ∈ u.asIdeal) : False := by
  obtain ⟨c, d, e⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes ha hb).2 hne)
  have e' := congrArg (Int.cast : ℤ → 𝓞 E) e
  push_cast at e'
  refine u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← e']
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

private theorem seenShape_nat_mem_cj {E : Type} [Field E] [NumberField E] [IsCMField E] {u : Plc E} {m : ℕ}
    (h : (m : 𝓞 E) ∈ u.asIdeal) : (m : 𝓞 E) ∈ (UpperTheory.Gal.CertificateRingHomMap.cj u).asIdeal := by
  have e := (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) u)
  rw [e, Ideal.mem_comap, map_natCast]
  exact h

theorem UpperTheory.Gal.W2.Seed.pSeenShape :
    StabKer → SiteFact → CenFacts → LevBasic → UpperTheory.Gal.CertificateRingHomMap.LocComm → SeenShape := by
  intro hSK hSF hCF hLB hc E _ _ _ A n p _ S F x U w₀ Up V hodd hsc hgen hoff hq₀ r W haux N hrN hstab L hw Ty hty g θ hs
  have key : ∀ k, Stab F V k → k ∈ S.L.KN r → k ∈ Ty.kerK :=
    hSK E A n p S F x U w₀ Up V hodd hsc hgen hoff hq₀ r W haux N hrN hstab L hw Ty hty
  rcases hs with ⟨hd, hst, hr, hθ⟩ | ⟨w, σ, i, B, hfree, hqr, hK, ⟨hi, hgK, ⟨hws, t, z, ht, hz, hh⟩, -⟩, hB, hθ⟩
  · refine ⟨?_, Or.inl ⟨hd, key _ hst hr, hθ⟩⟩
    rw [hd.1]
    exact fun k hk => key k (hstab k hk) (KN_anti hrN hk)
  · have hqw : ((σ.q : ℕ) : 𝓞 E) ∈ w.asIdeal := σ.atp.le (Ideal.subset_span (Set.mem_insert _ _))
    have hpp : p.Prime := Fact.out
    have hpw : (p : 𝓞 E) ∉ w.asIdeal := fun h => seenShape_not_both σ.atp.prime hpp σ.atp.ne hqw h
    let w' : Spl E p := ⟨w, hws, hpw⟩
    have hrU : ∀ u ∈ W, (r : 𝓞 E) ∈ u.1.asIdeal := haux.half.above
    have hqU : ∀ u ∈ W, ((σ.q : ℕ) : 𝓞 E) ∉ u.1.asIdeal := fun u hu h =>
      seenShape_not_both σ.atp.prime haux.prime hqr h (hrU u hu)
    have hcen := hCF E A n hodd.pos x hgen σ.q σ.atp.prime σ.good.1 w hqw z hz
    have hap1 : ∀ u ∈ W, GlobalTheory.Cong.Apart w u.1 := fun u hu => ((hc E n u.1 u.2.1).2.1 w).2
      ⟨fun e => hqU u hu (e ▸ hqw), fun e => seenShape_not_both (u := w) σ.atp.prime haux.prime hqr hqw
        (e ▸ seenShape_nat_mem_cj (hrU u hu))⟩
    have hap2 : ∀ u ∈ W, GlobalTheory.Cong.Apart u.1 w := fun u hu => ((hc E n w hws).2.1 u.1).2
      ⟨fun e => hqU u hu (e ▸ hqw), fun e => hqU u hu (e ▸ seenShape_nat_mem_cj hqw)⟩
    have hσK : σ.K₀ ≤ S.L.KN r := by
      obtain ⟨-, h2, h3, -⟩ := hLB p S.D S.G S.L
      refine h2 _ _ _ _ σ.isLev (h3 r) (Ideal.mul_le_left.trans (Ideal.span_singleton_le_span_singleton.2 ?_))
      have hd : r ∣ ordCompl[σ.q] N.1 := Nat.dvd_ordCompl_of_dvd_not_dvd hrN fun h =>
        hqr ((Nat.prime_dvd_prime_iff_eq σ.atp.prime haux.prime).1 h)
      exact Nat.cast_dvd_cast hd
    have hzi : ∀ a, (z ^ i)⁻¹ * a = a * (z ^ i)⁻¹ := fun a =>
      ((Commute.pow_left (show Commute z a from hcen.1 a) i).inv_left).eq
    have hw0 : comp w₀ z = 1 := (hz w₀).2 (hfree.2.2.2.1 w₀ V.shape.mem)
    refine ⟨?_, Or.inr ⟨w', t, z, i, B, hfree, hap1, hi, ht, hz, hB, ?_, ?_, ?_, ?_, ?_, hθ⟩⟩
    · rw [hgK]
      exact fun k hk => key k (hK k hk) (hσK hk)
    · exact fun u hu => hcen.2 u fun h => seenShape_not_both σ.atp.prime hpp σ.atp.ne h hu
    · have e : (UpperTheory.Gal.CertificateRingHomMap.loc hws t * z ^ i)⁻¹ = UpperTheory.Gal.CertificateRingHomMap.loc hws t⁻¹ * (z ^ i)⁻¹ := by
        rw [_root_.mul_inv_rev, map_inv]
        exact hzi _
      rw [hh, (hty.fac w').2 t⁻¹, ← map_inv F.j, e, map_mul]
    · refine ⟨fun a => ?_, ?_⟩
      · obtain ⟨a', rfl⟩ := F.surj a
        rw [← map_mul, ← map_mul, hzi]
      · rw [hty.L_eq]
        refine ((hty.fac ⟨w₀, hw⟩).1 (z ^ i)⁻¹).trans ?_
        show comp w₀ (z ^ i)⁻¹ = 1
        rw [map_inv, map_pow, hw0, one_pow, inv_one]
    · intro u hu
      rw [hh, (hty.fac u).1, map_mul, map_pow, UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hws (hap2 u hu),
        hcen.2 _ (hqU u hu), one_pow, one_mul]
    · rw [hgK]
      exact hSF E A n p S F x hgen N w' σ (L w') (hty.fac w')
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PStabKer
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pStabKer :
    FacEq → KNFact → CongGrpEx → StabKer := by
  intro _ hKN hCG E _ _ _ A n p _ S F x U w₀ Up V _ _ _ _ _ r W haux N _ _ L hw Ty hTy k hk hkr
  obtain ⟨k', hk', hlev, hJ, hχ⟩ := hk
  have hK : k ∈ Ty.K := by
    refine (hTy.K_iff k).2 ⟨⟨k', hk', hlev⟩, fun w hwW => ?_⟩
    have hr : (r : 𝓞 E) ∈ w.1.asIdeal := haux.half.above w hwW
    obtain ⟨K, hK, -, -, -, -, hIw, -⟩ := hCG E n r haux.prime.pos w.1
    have hf := hKN E A n p S F w (L w) (hTy.fac w) r haux.prime haux.good hr r haux.prime.pos K hK
    exact hIw hr (hf.2 k hkr)
  refine (Ty.mem_kerK k).2 ⟨hK, ?_⟩
  have hpr : Ty.L.pr k = comp w₀ k' := by
    rw [hTy.L_eq, ← hk']
    exact (hTy.fac ⟨w₀, hw⟩).1 k'
  refine (hTy.ψ_eq _ ⟨comp w₀ (F.th k'), hJ⟩ ?_).trans hχ
  simp only [hpr, th_eq F, CertificateRingHomMap.comp_th, CertificateRingHomMap.invT_val]
end

