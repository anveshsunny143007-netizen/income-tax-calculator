from fastapi import FastAPI, Form, Request
from fastapi.responses import HTMLResponse, StreamingResponse
from fastapi.templating import Jinja2Templates
from fastapi.staticfiles import StaticFiles  # <--- ADD THIS NEW IMPORT
import json
import io
from datetime import datetime
from reportlab.lib.pagesizes import A4
from reportlab.pdfgen import canvas
from reportlab.lib.units import inch
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import Table, TableStyle
from reportlab.lib import colors
import math
import requests
import re
import html
import cloudscraper
from bs4 import BeautifulSoup

app = FastAPI()

# --- ADD THIS NEW LINE right below app = FastAPI() ---
app.mount("/static", StaticFiles(directory="."), name="static")

templates = Jinja2Templates(directory="templates")

with open("taxdata.json") as f:
    all_tax_data = json.load(f)

def get_base_tax(taxable_income, slabs):
    tax = 0
    previous_limit = 0
    for slab in slabs:
        limit = slab["limit"]
        rate = slab["rate"]
        taxable_amount = max(min(taxable_income, limit) - previous_limit, 0)
        tax += taxable_amount * rate
        if taxable_income <= limit:
            break
        previous_limit = limit
    return tax

def get_tax_at_threshold(threshold, slab_income, stcg, ltcg, crypto_income, regime_slabs, stcg_rate, ltcg_rate, ltcg_exemption, basic_exemption=0):
    total = slab_income + stcg + ltcg + max(0, crypto_income)
    excess = total - threshold
    
    reduced_slab = slab_income
    reduced_stcg = stcg
    reduced_ltcg = ltcg
    reduced_crypto = max(0, crypto_income)
    
    if excess > 0:
        drop = min(reduced_slab, excess)
        reduced_slab -= drop
        excess -= drop
    if excess > 0:
        drop = min(reduced_stcg, excess)
        reduced_stcg -= drop
        excess -= drop
    if excess > 0:
        drop = min(reduced_ltcg, excess)
        reduced_ltcg -= drop
        excess -= drop
    if excess > 0:
        drop = min(reduced_crypto, excess)
        reduced_crypto -= drop
        excess -= drop
        
    unexhausted_bel = max(0, basic_exemption - reduced_slab)
    taxable_stcg = reduced_stcg
    taxable_ltcg = max(0, reduced_ltcg - ltcg_exemption)

    if unexhausted_bel > 0:
        setoff_stcg = min(taxable_stcg, unexhausted_bel)
        taxable_stcg -= setoff_stcg
        unexhausted_bel -= setoff_stcg
        
        setoff_ltcg = min(taxable_ltcg, unexhausted_bel)
        taxable_ltcg -= setoff_ltcg

    tax_slab = get_base_tax(reduced_slab, regime_slabs)
    tax_stcg = taxable_stcg * stcg_rate
    tax_ltcg = taxable_ltcg * ltcg_rate
    tax_crypto = reduced_crypto * 0.30
    return tax_slab + tax_stcg + tax_ltcg + tax_crypto

def calculate_surcharge_and_relief(total_taxable_income, slab_income, stcg, ltcg, crypto_income, base_tax, surcharge_slabs, regime_slabs, stcg_rate, ltcg_rate, ltcg_exemption, basic_exemption=0):
    surcharge_rate = 0
    threshold = 0
    for slab in surcharge_slabs:
        if total_taxable_income > slab["limit"]:
            threshold = slab["limit"]
            surcharge_rate = slab["rate"]
        else:
            break
            
    if surcharge_rate == 0:
        return 0, 0
        
    surcharge_rate_cg = min(surcharge_rate, 0.15)
    other_income = slab_income + crypto_income
    surcharge_rate_other = surcharge_rate
    
    if total_taxable_income > 20000000 and other_income <= 20000000:
        surcharge_rate_other = min(surcharge_rate, 0.15)
    
    unexhausted_bel = max(0, basic_exemption - slab_income)
    taxable_stcg = stcg
    taxable_ltcg = max(0, ltcg - ltcg_exemption)

    if unexhausted_bel > 0:
        setoff_stcg = min(taxable_stcg, unexhausted_bel)
        taxable_stcg -= setoff_stcg
        unexhausted_bel -= setoff_stcg
        
        setoff_ltcg = min(taxable_ltcg, unexhausted_bel)
        taxable_ltcg -= setoff_ltcg

    tax_stcg = taxable_stcg * stcg_rate
    tax_ltcg = taxable_ltcg * ltcg_rate
    tax_cg_total = tax_stcg + tax_ltcg
    
    tax_other = max(0, base_tax - tax_cg_total)
    actual_tax_cg = base_tax - tax_other
    
    surcharge = (tax_other * surcharge_rate_other) + (actual_tax_cg * surcharge_rate_cg)
    tax_at_threshold = get_tax_at_threshold(threshold, slab_income, stcg, ltcg, crypto_income, regime_slabs, stcg_rate, ltcg_rate, ltcg_exemption, basic_exemption)
        
    threshold_surcharge_rate = 0
    for slab in surcharge_slabs:
        if threshold > slab["limit"]:
            threshold_surcharge_rate = slab["rate"]
            
    threshold_surcharge_rate_cg = min(threshold_surcharge_rate, 0.15)
    threshold_surcharge_rate_other = threshold_surcharge_rate
    
    if threshold > 20000000 and other_income <= 20000000:
        threshold_surcharge_rate_other = min(threshold_surcharge_rate, 0.15)
    
    cg_ratio = actual_tax_cg / base_tax if base_tax > 0 else 0
    tax_threshold_cg = tax_at_threshold * cg_ratio
    tax_threshold_other = tax_at_threshold - tax_threshold_cg
            
    surcharge_at_threshold = (tax_threshold_other * threshold_surcharge_rate_other) + (tax_threshold_cg * threshold_surcharge_rate_cg)
    max_tax_allowed = tax_at_threshold + surcharge_at_threshold + (total_taxable_income - threshold)
    current_total_tax = base_tax + surcharge
    
    marginal_relief = 0
    if current_total_tax > max_tax_allowed:
        marginal_relief = current_total_tax - max_tax_allowed
        
    return surcharge - marginal_relief, marginal_relief

def calculate_new_regime(salary, business, rental, interest, dividend, foreign, other, stcg, ltcg, crypto_income, home_loan_interest, year_data):
    effective_crypto = max(0, crypto_income) 
    
    std_deduction_claimed = min(salary, year_data["standard_deduction"])
    taxable_salary = max(0, salary - std_deduction_claimed)
    
    house_property_income = (rental * 0.70) - home_loan_interest
    taxable_rental = max(0, house_property_income) 

    gross_slab_income = taxable_salary + business + taxable_rental + interest + dividend + foreign + other
    slab_income = gross_slab_income

    stcg_rate = year_data.get("stcg_rate", 0.20)
    ltcg_rate = year_data.get("ltcg_rate", 0.125)
    ltcg_exemption = year_data.get("ltcg_exemption", 125000)
    basic_exemption = year_data["new_regime_slabs"][0]["limit"]

    unexhausted_bel = max(0, basic_exemption - slab_income)
    taxable_stcg = stcg
    taxable_ltcg = max(0, ltcg - ltcg_exemption)

    if unexhausted_bel > 0:
        setoff_stcg = min(taxable_stcg, unexhausted_bel)
        taxable_stcg -= setoff_stcg
        unexhausted_bel -= setoff_stcg
        
        setoff_ltcg = min(taxable_ltcg, unexhausted_bel)
        taxable_ltcg -= setoff_ltcg
        unexhausted_bel -= setoff_ltcg

    breakdown = []
    slab_tax = 0
    previous_limit = 0

    for slab in year_data["new_regime_slabs"]:
        limit = slab["limit"]
        rate = slab["rate"]
        taxable_amount = max(min(slab_income, limit) - previous_limit, 0)
        tax_part = taxable_amount * rate
        if taxable_amount > 0:
            breakdown.append({"range": f"{previous_limit:,} - {limit:,}", "amount": taxable_amount, "rate": f"{int(rate*100)}%", "tax": tax_part})
        slab_tax += tax_part
        if slab_income <= limit:
            break
        previous_limit = limit

    stcg_tax = taxable_stcg * stcg_rate
    ltcg_tax = taxable_ltcg * ltcg_rate
    crypto_tax = effective_crypto * 0.30
    special_tax = stcg_tax + ltcg_tax + crypto_tax

    total_taxable_income = slab_income + stcg + ltcg + effective_crypto
    total_tax_before_rebate = slab_tax + special_tax

    tax_eligible_for_rebate = slab_tax + stcg_tax + crypto_tax 
    
    rebate = 0
    marginal_relief_87a = 0
    
    if total_taxable_income <= year_data["new_rebate_limit"]:
        rebate = tax_eligible_for_rebate 
        tax_after_rebate = total_tax_before_rebate - rebate
    else:
        excess_income = total_taxable_income - year_data["new_rebate_limit"]
        max_allowed_tax_on_eligible = excess_income
        if tax_eligible_for_rebate > max_allowed_tax_on_eligible:
            marginal_relief_87a = tax_eligible_for_rebate - max_allowed_tax_on_eligible
            rebate = 0  # FIX: Reset standard rebate to 0 so the UI doesn't double-count
            tax_after_rebate = total_tax_before_rebate - marginal_relief_87a # FIX: Subtract the relief exactly once
        else:
            tax_after_rebate = total_tax_before_rebate

    net_surcharge, marginal_relief_surcharge = calculate_surcharge_and_relief(
        total_taxable_income, slab_income, stcg, ltcg, effective_crypto, tax_after_rebate, 
        year_data["new_surcharge_slabs"], year_data["new_regime_slabs"], stcg_rate, ltcg_rate, ltcg_exemption, basic_exemption
    )
    cess = (tax_after_rebate + net_surcharge) * 0.04
    final_tax = tax_after_rebate + net_surcharge + cess

    return {
        "standard_deduction": std_deduction_claimed, "taxable_salary": taxable_salary, "taxable_rental": taxable_rental,
        "gross_slab_income": gross_slab_income, "slab_income": slab_income, "stcg_tax": stcg_tax, "ltcg_tax": ltcg_tax, "crypto_tax": crypto_tax,
        "tax_before_rebate": total_tax_before_rebate, "rebate": rebate + marginal_relief_87a, "marginal_relief_87a": marginal_relief_87a,
        "tax_after_rebate": tax_after_rebate, "surcharge": net_surcharge + marginal_relief_surcharge, 
        "marginal_relief_surcharge": marginal_relief_surcharge, "net_surcharge": net_surcharge,
        "cess": cess, "final_tax": final_tax, "breakdown": breakdown
    }

def calculate_old_regime(salary, business, rental, interest, dividend, foreign, other, stcg, ltcg, crypto_income, 
                         deduction_80c, deduction_80d, nps_80ccd1b, deduction_80e, deduction_80g_100, deduction_80g_50, other_deductions, 
                         home_loan_interest, basic_salary, hra_received, rent_paid, is_metro, professional_tax, lta_exemption, sec10_allowances,
                         year_data, age_group):
    
    effective_crypto = max(0, crypto_income) 
    
    hra_exemption = 0
    if basic_salary > 0 and hra_received > 0 and rent_paid > 0:
        cond1 = hra_received
        cond2 = max(0, rent_paid - (0.10 * basic_salary))
        cond3 = 0.50 * basic_salary if is_metro == 'metro' else 0.40 * basic_salary
        hra_exemption = min(cond1, cond2, cond3)
    
    lta_exemption = max(0, lta_exemption)
    
    total_exemptions_sec10 = min(salary, hra_exemption + lta_exemption + sec10_allowances)
    salary_post_exemptions = max(0, salary - total_exemptions_sec10)

    old_std_limit = year_data.get("old_standard_deduction", 50000)
    professional_tax = min(professional_tax, 2500)
    
    total_sec16_deductions = min(salary_post_exemptions, old_std_limit + professional_tax)
    taxable_salary = max(0, salary_post_exemptions - total_sec16_deductions)

    house_property_income = (rental * 0.70) - home_loan_interest
    taxable_rental = max(house_property_income, -200000)

    if age_group in ["senior", "super_senior"]:
        deduction_80tta_ttb = min(interest, 50000)
    else:
        deduction_80tta_ttb = min(interest, 10000)

    deduction_80c = min(max(deduction_80c, 0), 150000)
    max_80d = 50000 if age_group in ["senior", "super_senior"] else 25000
    deduction_80d = min(max(deduction_80d, 0), max_80d)
    nps_deduction = min(max(nps_80ccd1b, 0), 50000)
    deduction_80e = max(deduction_80e, 0)
    other_deductions = max(other_deductions, 0)
    
    gross_slab_income = taxable_salary + business + taxable_rental + interest + dividend + foreign + other
    
    base_chapter_via = deduction_80c + deduction_80d + nps_deduction + deduction_80tta_ttb + deduction_80e + other_deductions
    agti = max(0, gross_slab_income - base_chapter_via)
    
    limit_10_percent_agti = 0.10 * agti
    allowed_80g_50 = min(max(deduction_80g_50, 0), limit_10_percent_agti) * 0.50
    allowed_80g_100 = max(deduction_80g_100, 0)
    total_80g_deduction = allowed_80g_100 + allowed_80g_50

    total_chapter_via = base_chapter_via + total_80g_deduction
    
    slab_income = max(gross_slab_income - total_chapter_via, 0)
    actual_deductions_claimed = gross_slab_income - slab_income if gross_slab_income > 0 else 0

    stcg_rate = year_data.get("stcg_rate", 0.20)
    ltcg_rate = year_data.get("ltcg_rate", 0.125)
    ltcg_exemption = year_data.get("ltcg_exemption", 125000)
    slabs = year_data["old_regime_slabs"][age_group]
    basic_exemption = slabs[0]["limit"]

    unexhausted_bel = max(0, basic_exemption - slab_income)
    taxable_stcg = stcg
    taxable_ltcg = max(0, ltcg - ltcg_exemption)

    if unexhausted_bel > 0:
        setoff_stcg = min(taxable_stcg, unexhausted_bel)
        taxable_stcg -= setoff_stcg
        unexhausted_bel -= setoff_stcg
        
        setoff_ltcg = min(taxable_ltcg, unexhausted_bel)
        taxable_ltcg -= setoff_ltcg

    breakdown = []
    slab_tax = 0
    previous_limit = 0

    for slab in slabs:
        limit = slab["limit"]
        rate = slab["rate"]
        taxable_amount = max(min(slab_income, limit) - previous_limit, 0)
        tax_part = taxable_amount * rate
        if taxable_amount > 0:
            breakdown.append({"range": f"{previous_limit:,} - {limit:,}", "amount": taxable_amount, "rate": f"{int(rate*100)}%", "tax": tax_part})
        slab_tax += tax_part
        if slab_income <= limit:
            break
        previous_limit = limit

    stcg_tax = taxable_stcg * stcg_rate
    ltcg_tax = taxable_ltcg * ltcg_rate
    crypto_tax = effective_crypto * 0.30
    special_tax = stcg_tax + ltcg_tax + crypto_tax

    total_taxable_income = slab_income + stcg + ltcg + effective_crypto
    total_tax_before_rebate = slab_tax + special_tax

    tax_eligible_for_rebate = slab_tax + stcg_tax + crypto_tax
    
    rebate = 0
    if total_taxable_income <= year_data["old_rebate_limit"]:
        rebate = min(tax_eligible_for_rebate, 12500)
        
    tax_after_rebate = total_tax_before_rebate - rebate

    net_surcharge, marginal_relief_surcharge = calculate_surcharge_and_relief(
        total_taxable_income, slab_income, stcg, ltcg, effective_crypto, tax_after_rebate, 
        year_data["old_surcharge_slabs"], slabs, stcg_rate, ltcg_rate, ltcg_exemption, basic_exemption
    )
    cess = (tax_after_rebate + net_surcharge) * 0.04
    final_tax = tax_after_rebate + net_surcharge + cess

    return {
        "hra_exemption": hra_exemption, "lta_exemption": lta_exemption, "professional_tax": professional_tax,
        "standard_deduction": min(salary_post_exemptions, old_std_limit), "home_loan_loss_setoff": min(0, taxable_rental), 
        "80tta_ttb_deduction": deduction_80tta_ttb, "nps_deduction": nps_deduction, "deduction_80g": total_80g_deduction,
        "taxable_salary": taxable_salary, "taxable_rental": taxable_rental, "total_deductions": actual_deductions_claimed,
        "gross_slab_income": gross_slab_income, "slab_income": slab_income, 
        "stcg_tax": stcg_tax, "ltcg_tax": ltcg_tax, "crypto_tax": crypto_tax,
        "tax_before_rebate": total_tax_before_rebate, "rebate": rebate, "tax_after_rebate": tax_after_rebate,
        "surcharge": net_surcharge + marginal_relief_surcharge, "marginal_relief_surcharge": marginal_relief_surcharge,
        "net_surcharge": net_surcharge, "cess": cess, "final_tax": final_tax, "breakdown": breakdown
    }

def generate_tax_pdf(income, income_breakdown, year, comparison, new_data, old_data, report_type):
    buffer = io.BytesIO()
    p = canvas.Canvas(buffer, pagesize=A4)
    width, height = A4

    # Font Handling
    try:
        pdfmetrics.registerFont(TTFont("DejaVu", "DejaVuSans.ttf"))
        font_base = "DejaVu"
        font_bold = "DejaVu" 
    except:
        font_base = "Helvetica"
        font_bold = "Helvetica-Bold"

    # Helper function to draw headers on new pages
    def draw_watermark_and_header(canvas_obj):
        # Watermark
        canvas_obj.saveState()
        canvas_obj.setFont(font_bold, 70)
        canvas_obj.setFillGray(0.96)
        canvas_obj.translate(width/2, height/2)
        canvas_obj.rotate(45)
        canvas_obj.drawCentredString(0, 0, "CONFIDENTIAL REPORT")
        canvas_obj.restoreState()

        # Corporate Top Banner
        canvas_obj.setFillColor(colors.HexColor("#0a2540")) 
        canvas_obj.rect(0, height - 90, width, 90, fill=1, stroke=0)
        
        text_start_x = 40
        try:
            canvas_obj.drawImage("logo.png", 40, height - 75, width=60, height=60, preserveAspectRatio=True, mask='auto')
            text_start_x = 120
        except:
            pass 

        canvas_obj.setFillColor(colors.white)
        canvas_obj.setFont(font_bold, 22)
        canvas_obj.drawString(text_start_x, height - 45, "Institutional Tax Advisory")
        canvas_obj.setFont(font_base, 11)
        canvas_obj.drawString(text_start_x, height - 65, f"Assessment Framework: FY {year}  |  Generated: {datetime.now().strftime('%d %b %Y, %H:%M')}")
        return height - 130

    # Draw Page 1 Header
    y = draw_watermark_and_header(p)

    # --- 1. Executive Recommendation Box ---
    best_regime = "New Regime" if new_data["final_tax"] < old_data["final_tax"] else "Old Regime"
    savings = abs(new_data["final_tax"] - old_data["final_tax"])

    p.setFillColor(colors.HexColor("#f4f9ff"))
    p.setStrokeColor(colors.HexColor("#1976d2"))
    p.roundRect(40, y - 80, width - 80, 80, 6, fill=1, stroke=1)

    p.setFillColor(colors.HexColor("#0a2540"))
    p.setFont(font_bold, 15)
    p.drawString(60, y - 30, f"EXECUTIVE DIRECTIVE: {best_regime.upper()} OPTIMAL")

    p.setFont(font_base, 12)
    p.setFillColor(colors.HexColor("#4a5568"))
    p.drawString(60, y - 55, f"Adopting the {best_regime} structural framework mathematically results")
    p.drawString(60, y - 70, f"in a net legal reduction of tax liability by Rs. {savings:,.0f}.")
    
    y -= 120

    # --- 2. Core Metrics Table ---
    p.setFillColor(colors.HexColor("#0a2540"))
    p.setFont(font_bold, 14)
    p.drawString(40, y, "Fiscal Baseline & Regime Comparison")
    y -= 25

    table_data = [
        ["Structural Metric", "New Regime Model", "Old Regime Model"],
        ["Gross Base Income", f"Rs. {new_data['gross_slab_income']:,.0f}", f"Rs. {old_data['gross_slab_income']:,.0f}"],
        ["Total Allowed Deductions", f"Rs. {new_data['standard_deduction']:,.0f}", f"Rs. {old_data['total_deductions'] + old_data['standard_deduction']:,.0f}"],
        ["Net Taxable Slab Pool", f"Rs. {new_data['slab_income']:,.0f}", f"Rs. {old_data['slab_income']:,.0f}"],
        ["FINAL NET LIABILITY", f"Rs. {new_data['final_tax']:,.0f}", f"Rs. {old_data['final_tax']:,.0f}"]
    ]

    table = Table(table_data, colWidths=[200, 150, 150])
    table.setStyle(TableStyle([
        ('BACKGROUND', (0,0), (-1,0), colors.HexColor('#1976d2')),
        ('TEXTCOLOR', (0,0), (-1,0), colors.white),
        ('FONTNAME', (0,0), (-1,0), font_bold),
        ('FONTSIZE', (0,0), (-1,0), 11),
        ('BOTTOMPADDING', (0,0), (-1,0), 10),
        ('TOPPADDING', (0,0), (-1,0), 10),
        ('BACKGROUND', (0,1), (-1,-2), colors.HexColor('#ffffff')),
        ('TEXTCOLOR', (0,1), (-1,-1), colors.HexColor('#2d3436')),
        ('FONTNAME', (0,1), (-1,-1), font_base),
        ('FONTSIZE', (0,1), (-1,-1), 11),
        ('BOTTOMPADDING', (0,1), (-1,-1), 8),
        ('TOPPADDING', (0,1), (-1,-1), 8),
        ('BACKGROUND', (0,2), (-1,2), colors.HexColor('#f8f9fa')),
        ('BACKGROUND', (0,-1), (-1,-1), colors.HexColor('#e3f2fd')),
        ('FONTNAME', (0,-1), (-1,-1), font_bold),
        ('TEXTCOLOR', (0,-1), (-1,-1), colors.HexColor('#0a2540')),
        ('ALIGN', (1,0), (-1,-1), 'RIGHT'),
        ('GRID', (0,0), (-1,-1), 0.5, colors.HexColor('#dfe6e9')),
    ]))
    
    table.wrapOn(p, width, height)
    table.drawOn(p, 40, y - table._height)
    y = y - table._height - 40

    # --- 3. Special Capital Assets (Printed on both Standard & Detailed if present) ---
    if income_breakdown.get('STCG', 0) > 0 or income_breakdown.get('LTCG', 0) > 0 or income_breakdown.get('Crypto (VDA)', 0) > 0:
        p.setFillColor(colors.HexColor("#0a2540"))
        p.setFont(font_bold, 14)
        p.drawString(40, y, "Special Rate Capital Assets (Sec 111A/112A/115BBH)")
        y -= 25
        
        p.setFont(font_base, 11)
        p.setFillColor(colors.HexColor("#4a5568"))
        if income_breakdown.get('STCG', 0) > 0:
            p.drawString(50, y, f"• Short Term Capital Gains: Rs. {income_breakdown['STCG']:,.0f} (Calculated Tax: Rs. {new_data['stcg_tax']:,.0f})")
            y -= 20
        if income_breakdown.get('LTCG', 0) > 0:
            p.drawString(50, y, f"• Long Term Capital Gains: Rs. {income_breakdown['LTCG']:,.0f} (Calculated Tax: Rs. {new_data['ltcg_tax']:,.0f})")
            y -= 20
        if income_breakdown.get('Crypto (VDA)', 0) > 0:
            p.drawString(50, y, f"• Virtual Digital Assets: Rs. {income_breakdown['Crypto (VDA)']:,.0f} (Calculated Tax: Rs. {new_data['crypto_tax']:,.0f})")
            y -= 30

    # --- 4. ADVANCED ADVISORY SECTION (Detailed Only) ---
    if report_type == "detailed":
        
        # Check if we need a new page before drawing the detailed section
        if y < 250:
            p.showPage()
            y = draw_watermark_and_header(p)
            
        # A. Deductions Breakdown (Old Regime)
        p.setFillColor(colors.HexColor("#0a2540"))
        p.setFont(font_bold, 14)
        p.drawString(40, y, "Itemized Exemption & Deduction Breakdown (Old Regime)")
        y -= 25
        
        p.setFont(font_base, 11)
        p.setFillColor(colors.HexColor("#4a5568"))
        
        deds = []
        if old_data.get('hra_exemption', 0) > 0: deds.append(f"HRA Exemption (Sec 10): Rs. {old_data['hra_exemption']:,.0f}")
        if old_data.get('lta_exemption', 0) > 0: deds.append(f"LTA Exemption (Sec 10): Rs. {old_data['lta_exemption']:,.0f}")
        if old_data.get('professional_tax', 0) > 0: deds.append(f"Professional Tax (Sec 16): Rs. {old_data['professional_tax']:,.0f}")
        if old_data.get('home_loan_loss_setoff', 0) < 0: deds.append(f"Home Loan Set-Off (Sec 24b): Rs. {abs(old_data['home_loan_loss_setoff']):,.0f}")
        if old_data.get('80tta_ttb_deduction', 0) > 0: deds.append(f"Savings Interest (Sec 80TTA/TTB): Rs. {old_data['80tta_ttb_deduction']:,.0f}")
        
        total_chap_via = old_data.get('total_deductions', 0) - old_data.get('80tta_ttb_deduction', 0)
        if total_chap_via > 0: deds.append(f"Chapter VI-A Claims (80C, 80D, 80G, NPS): Rs. {total_chap_via:,.0f}")

        if not deds:
            p.drawString(50, y, "• No structural exemptions or deductions claimed.")
            y -= 20
        else:
            for ded in deds:
                p.drawString(50, y, f"• {ded}")
                y -= 20

        y -= 20

        # B. Slab-by-Slab Calculation Table
        # Check page bounds again before drawing the table
        if y < 200:
            p.showPage()
            y = draw_watermark_and_header(p)

        p.setFillColor(colors.HexColor("#0a2540"))
        p.setFont(font_bold, 14)
        p.drawString(40, y, f"Mathematical Tax Breakdown (Optimal: {best_regime})")
        y -= 20

        slab_data = [["Income Bracket", "Tax Rate", "Calculated Liability"]]
        target_data = new_data if best_regime == "New Regime" else old_data
        
        for slab in target_data['breakdown']:
            slab_data.append([slab['range'], slab['rate'], f"Rs. {slab['tax']:,.0f}"])

        # Add Surcharge, Rebate, and Cess to the table to make it comprehensive
        if target_data.get('rebate', 0) > 0:
            slab_data.append(["Sec 87A Mitigation (Rebate)", "Fixed", f"- Rs. {target_data['rebate']:,.0f}"])
        if target_data.get('surcharge', 0) > 0:
            slab_data.append(["HNI Surcharge Applied", "Scaled", f"+ Rs. {target_data['surcharge']:,.0f}"])
        
        slab_data.append(["Health & Education Cess", "4%", f"+ Rs. {target_data['cess']:,.0f}"])
        slab_data.append(["Total Bracket Liability", "NET", f"Rs. {target_data['final_tax']:,.0f}"])

        slab_table = Table(slab_data, colWidths=[200, 150, 150])
        slab_table.setStyle(TableStyle([
            ('BACKGROUND', (0,0), (-1,0), colors.HexColor('#635bff')),
            ('TEXTCOLOR', (0,0), (-1,0), colors.white),
            ('FONTNAME', (0,0), (-1,0), font_bold),
            ('FONTSIZE', (0,0), (-1,0), 10),
            ('ALIGN', (1,0), (-1,-1), 'RIGHT'),
            ('GRID', (0,0), (-1,-1), 0.5, colors.HexColor('#dfe6e9')),
            ('FONTNAME', (0,1), (-1,-1), font_base),
            ('FONTSIZE', (0,1), (-1,-1), 10),
            ('PADDING', (0,0), (-1,-1), 8),
            # Bold the bottom row
            ('FONTNAME', (0,-1), (-1,-1), font_bold),
            ('BACKGROUND', (0,-1), (-1,-1), colors.HexColor('#f4f9ff')),
            ('TEXTCOLOR', (0,-1), (-1,-1), colors.HexColor('#0a2540')),
        ]))
        
        slab_table.wrapOn(p, width, height)
        slab_table.drawOn(p, 40, y - slab_table._height)
        y -= (slab_table._height + 30)

    # --- 5. Footer Disclaimer (Printed on every final page) ---
    p.setFont(font_base, 8)
    p.setFillColor(colors.HexColor("#a0aec0"))
    p.drawString(40, 40, "DISCLAIMER: This document is an algorithmic projection and does not constitute legally binding tax advice.")
    p.drawString(40, 30, "Please consult a registered Chartered Accountant before filing official returns with the Income Tax Department.")
    
    p.showPage()
    p.save()
    buffer.seek(0)
    return buffer

# ---------------- ROUTES ---------------- #
@app.get("/", response_class=HTMLResponse)
def home(request: Request):
    return templates.TemplateResponse(request=request, name="index.html", context={"tax_data": all_tax_data})

@app.post("/calculate", response_class=HTMLResponse)
def calculate(
    request: Request,
    year: str = Form(...), age_group: str = Form(...),
    salary_income: float = Form(0), business_income: float = Form(0), rental_income: float = Form(0),
    interest_income: float = Form(0), dividend_income: float = Form(0), foreign_income: float = Form(0),
    other_income_val: float = Form(0), stcg_income: float = Form(0), ltcg_income: float = Form(0), crypto_income: float = Form(0),
    basic_salary: float = Form(0), hra_received: float = Form(0), rent_paid: float = Form(0), is_metro: str = Form("non_metro"),
    lta_exemption: float = Form(0), professional_tax: float = Form(0), home_loan_interest: float = Form(0),
    deduction_80c: float = Form(0), deduction_80d: float = Form(0), nps_80ccd1b: float = Form(0),
    deduction_80e: float = Form(0), deduction_80g_100: float = Form(0), deduction_80g_50: float = Form(0),
    other_deductions: float = Form(0), growth_rate: float = Form(10.0)
):
    actual_crypto_for_gross = max(0, crypto_income)
    
    total_gross_income = (salary_income + business_income + rental_income + interest_income + 
                          dividend_income + foreign_income + other_income_val + 
                          stcg_income + ltcg_income + actual_crypto_for_gross)

    income_breakdown = {
        "Salary": salary_income, "Business / Prof": business_income, "Rental": rental_income,
        "Interest": interest_income, "Dividend": dividend_income, "Foreign": foreign_income, "Other": other_income_val,
        "STCG": stcg_income, "LTCG": ltcg_income, "Crypto (VDA)": actual_crypto_for_gross
    }

    if total_gross_income <= 0:
        return templates.TemplateResponse(request=request, name="index.html", context={"error": "Total income must be > 0.", "tax_data": all_tax_data})

    comparison = []
    lowest_tax = float("inf")
    best_year = None
    
    for fy, data in all_tax_data.items():
        new_tax = calculate_new_regime(salary_income, business_income, rental_income, interest_income, dividend_income, foreign_income, other_income_val, stcg_income, ltcg_income, crypto_income, home_loan_interest, data)["final_tax"]
        old_tax = calculate_old_regime(salary_income, business_income, rental_income, interest_income, dividend_income, foreign_income, other_income_val, stcg_income, ltcg_income, crypto_income, deduction_80c, deduction_80d, nps_80ccd1b, deduction_80e, deduction_80g_100, deduction_80g_50, other_deductions, home_loan_interest, basic_salary, hra_received, rent_paid, is_metro, professional_tax, lta_exemption, 0, data, age_group)["final_tax"]
        better_option = "New Regime" if new_tax < old_tax else "Old Regime"
        if new_tax == old_tax: better_option = "Equal"
        
        min_tax_this_year = min(new_tax, old_tax)
        if min_tax_this_year < lowest_tax:
            lowest_tax = min_tax_this_year
            best_year = fy
        comparison.append({"year": fy, "new_tax": new_tax, "old_tax": old_tax, "better": better_option})

    comparison = sorted(comparison, key=lambda x: x["year"])
    years_list = [row["year"] for row in comparison]
    new_taxes_list = [row["new_tax"] for row in comparison]
    old_taxes_list = [row["old_tax"] for row in comparison]

    selected_tax_data = all_tax_data[year]
    new_data = calculate_new_regime(salary_income, business_income, rental_income, interest_income, dividend_income, foreign_income, other_income_val, stcg_income, ltcg_income, crypto_income, home_loan_interest, selected_tax_data)
    old_data = calculate_old_regime(salary_income, business_income, rental_income, interest_income, dividend_income, foreign_income, other_income_val, stcg_income, ltcg_income, crypto_income, deduction_80c, deduction_80d, nps_80ccd1b, deduction_80e, deduction_80g_100, deduction_80g_50, other_deductions, home_loan_interest, basic_salary, hra_received, rent_paid, is_metro, professional_tax, lta_exemption, 0, selected_tax_data, age_group)
    
    better = "New Regime" if new_data["final_tax"] < old_data["final_tax"] else "Old Regime"
    tax_difference = abs(new_data["final_tax"] - old_data["final_tax"])
    current_best_tax = min(new_data["final_tax"], old_data["final_tax"])

    salary_optimization = None
    if salary_income > 0:
        sim_basic = salary_income * 0.50
        sim_hra_rec = sim_basic * 0.50
        sim_rent_paid = sim_hra_rec + (0.10 * sim_basic) 
        sim_lta = min(50000, salary_income * 0.05)
        sim_food = 26400 if salary_income > 500000 else 0
        sim_telecom = 24000 if salary_income > 500000 else 0
        
        sim_special = salary_income - (sim_basic + sim_hra_rec + sim_lta + sim_food + sim_telecom)
        if sim_special < 0: 
            sim_lta = 0; sim_food = 0; sim_telecom = 0
            sim_special = salary_income - (sim_basic + sim_hra_rec)

        sim_sec10_allowances = sim_food + sim_telecom
        sim_old_data = calculate_old_regime(
            salary_income, business_income, rental_income, interest_income, dividend_income, foreign_income, other_income_val, 
            stcg_income, ltcg_income, crypto_income,
            deduction_80c, deduction_80d, nps_80ccd1b, deduction_80e, deduction_80g_100, deduction_80g_50, other_deductions, 
            home_loan_interest, sim_basic, sim_hra_rec, sim_rent_paid, 'metro', professional_tax, sim_lta, sim_sec10_allowances, 
            selected_tax_data, age_group
        )
        opt_sim_tax = sim_old_data["final_tax"]
        if opt_sim_tax < current_best_tax:
            salary_optimization = {
                "current_basic": basic_salary, "current_hra": hra_received, "current_lta": lta_exemption,
                "current_special": max(0, salary_income - (basic_salary + hra_received + lta_exemption)),
                "sim_basic": sim_basic, "sim_hra": sim_hra_rec, "sim_lta": sim_lta, "sim_food": sim_food,
                "sim_telecom": sim_telecom, "sim_special": sim_special,
                "savings": current_best_tax - opt_sim_tax, "new_tax": opt_sim_tax
            }

    break_even_additional = 0
    break_even_total = 0
    is_break_even_possible = False
    roadmap_allocation = []
    max_80c_limit = 150000
    max_80d_limit = 50000 if age_group in ["senior", "super_senior"] else 25000
    max_nps_limit = 50000
    remaining_80c = max(max_80c_limit - deduction_80c, 0)
    remaining_80d = max(max_80d_limit - deduction_80d, 0)
    remaining_nps = max(max_nps_limit - nps_80ccd1b, 0)

    if better == "New Regime":
        low = 0; high = int(old_data['gross_slab_income']); best_extra = -1
        while low <= high:
            mid = (low + high) // 2
            test_old = calculate_old_regime(
                salary_income, business_income, rental_income, interest_income, dividend_income, foreign_income, other_income_val, 
                stcg_income, ltcg_income, crypto_income,
                deduction_80c, deduction_80d, nps_80ccd1b, deduction_80e, deduction_80g_100, deduction_80g_50, other_deductions + mid, home_loan_interest,
                basic_salary, hra_received, rent_paid, is_metro, professional_tax, lta_exemption, 0, selected_tax_data, age_group
            )
            if test_old["final_tax"] <= new_data["final_tax"]:
                best_extra = mid
                high = mid - 1 
            else:
                low = mid + 1
        if best_extra != -1:
            is_break_even_possible = True
            break_even_additional = best_extra
            break_even_total = old_data["total_deductions"] + best_extra
            target = break_even_additional
            if target > 0 and remaining_80c > 0:
                alloc = min(target, remaining_80c)
                roadmap_allocation.append(f"Invest ₹{alloc:,.0f} in Section 80C (ELSS, PPF, LIC)")
                target -= alloc
            if target > 0 and remaining_nps > 0:
                alloc = min(target, remaining_nps)
                roadmap_allocation.append(f"Invest ₹{alloc:,.0f} in NPS (80CCD(1B))")
                target -= alloc
            if target > 0 and remaining_80d > 0:
                alloc = min(target, remaining_80d)
                roadmap_allocation.append(f"Buy Health Insurance worth ₹{alloc:,.0f} (Section 80D)")
                target -= alloc
            if target > 0:
                roadmap_allocation.append(f"Claim ₹{target:,.0f} in other valid deductions (e.g., 80G Donations, 80E Education Loan)")

    future_projections = []
    proj_salary = salary_income
    proj_business = business_income
    growth_multiplier = 1 + (growth_rate / 100)
    
    curr_new_rebate_active = new_data["rebate"] > 0
    curr_old_rebate_active = old_data["rebate"] > 0
    
    for i in range(1, 6):
        proj_salary *= growth_multiplier
        proj_business *= growth_multiplier
        
        sim_basic = basic_salary * (growth_multiplier**i) if basic_salary else 0
        sim_hra = hra_received * (growth_multiplier**i) if hra_received else 0
        sim_rent = rent_paid * (growth_multiplier**i) if rent_paid else 0
        
        p_new = calculate_new_regime(proj_salary, proj_business, rental_income, interest_income, dividend_income, foreign_income, other_income_val, stcg_income, ltcg_income, crypto_income, home_loan_interest, selected_tax_data)
        p_old = calculate_old_regime(proj_salary, proj_business, rental_income, interest_income, dividend_income, foreign_income, other_income_val, stcg_income, ltcg_income, crypto_income, deduction_80c, deduction_80d, nps_80ccd1b, deduction_80e, deduction_80g_100, deduction_80g_50, other_deductions, home_loan_interest, sim_basic, sim_hra, sim_rent, is_metro, professional_tax, lta_exemption, 0, selected_tax_data, age_group)
        
        note = ""
        if curr_new_rebate_active and p_new["rebate"] == 0:
            note = "⚠️ 87A Rebate Lost"
            curr_new_rebate_active = False 
            
        future_projections.append({
            "year": f"Year +{i}",
            "income": proj_salary + proj_business + rental_income + interest_income + dividend_income + foreign_income + other_income_val + stcg_income + ltcg_income + actual_crypto_for_gross,
            "new_tax": p_new["final_tax"], "old_tax": p_old["final_tax"], "better": "New Regime" if p_new["final_tax"] < p_old["final_tax"] else "Old Regime",
            "note": note
        })

    harvesting_advice = []
    stcg_rate = selected_tax_data.get("stcg_rate", 0.20)
    ltcg_rate = selected_tax_data.get("ltcg_rate", 0.125)
    ltcg_exempt = selected_tax_data.get("ltcg_exemption", 125000)

    if stcg_income > 0:
        harvesting_advice.append(f"Tax-Loss Harvesting: You have ₹{stcg_income:,.0f} in STCG. If you book short-term capital losses (STCL) by selling poorly performing stocks, you can offset this STCG and save exactly ₹{stcg_income * stcg_rate:,.0f} ({int(stcg_rate*100)}%) on every rupee of loss booked.")
    if ltcg_income > ltcg_exempt:
        excess = ltcg_income - ltcg_exempt
        harvesting_advice.append(f"LTCG Offsetting: You exceeded the ₹{ltcg_exempt/100000:,.2f}L tax-free limit by ₹{excess:,.0f}. Booking unrealized Long-Term losses before March 31st will save you {ltcg_rate*100}% on this excess.")
    elif ltcg_income > 0 and ltcg_income < ltcg_exempt:
        room = ltcg_exempt - ltcg_income
        harvesting_advice.append(f"Tax-Gain Harvesting: You still have ₹{room:,.0f} of tax-free LTCG limit left. Sell and immediately re-buy profitable long-term stocks to permanently wipe out future taxes on this amount!")

    optimized_old = calculate_old_regime(
        salary_income, business_income, rental_income, interest_income, dividend_income, foreign_income, other_income_val, 
        stcg_income, ltcg_income, crypto_income,
        deduction_80c + remaining_80c, deduction_80d + remaining_80d, nps_80ccd1b + remaining_nps, deduction_80e, deduction_80g_100, deduction_80g_50, other_deductions, home_loan_interest, 
        basic_salary, hra_received, rent_paid, is_metro, professional_tax, lta_exemption, 0, selected_tax_data, age_group
    )
    saving_in_old = old_data["final_tax"] - optimized_old["final_tax"]

    optimizer = None
    ai_advice = {
        "title": f"{better} Recommended", "summary": f"{better} saves you ₹{tax_difference:,.0f} compared to the other regime.", "details": []
    }
    if better == "New Regime":
        ai_advice["details"] = ["Your combined Chapter VI-A deductions are relatively low.", "Higher basic exemption offsets the lack of 80C/80D."]
        explanation = "The New Regime is mathematically better because your claimed deductions do not compensate for the Old Regime's higher slab rates."
        if saving_in_old > 0:
            optimizer = {"saving_old": saving_in_old, "optimized_tax": optimized_old["final_tax"]}
    else:
        ai_advice["details"] = ["Your deductions heavily offset your taxable income.", "You successfully drop into a lower tax bracket."]
        explanation = "The Old Regime is better because your specific deductions and exemptions significantly reduce your taxable slab income."
        if saving_in_old > 0:
            optimizer = {"saving_old": saving_in_old, "optimized_tax": optimized_old["final_tax"]}
            roadmap_allocation.append(f"You are currently winning with the Old Regime! Maximizing your remaining limits can save you an additional ₹{saving_in_old:,.0f}.")
            if remaining_80c > 0: roadmap_allocation.append(f"Invest ₹{remaining_80c:,.0f} more in Section 80C")
            if remaining_nps > 0: roadmap_allocation.append(f"Invest ₹{remaining_nps:,.0f} more in NPS")
            if remaining_80d > 0: roadmap_allocation.append(f"Claim up to ₹{remaining_80d:,.0f} more in Health Insurance")

    new_effective_rate = (new_data["final_tax"] / total_gross_income) * 100 if total_gross_income > 0 else 0
    old_effective_rate = (old_data["final_tax"] / total_gross_income) * 100 if total_gross_income > 0 else 0
    surcharge_warning = "High income surcharge applied. Note: Maximum surcharge for Capital Gains (STCG/LTCG) is actively capped at 15%." if new_data["net_surcharge"] > 0 or old_data["net_surcharge"] > 0 else None

    return templates.TemplateResponse(request=request, name="result.html", context={
        "comparison": comparison, "best_year": best_year,
        "years": years_list, "new_taxes": new_taxes_list, "old_taxes": old_taxes_list, 
        "income": total_gross_income, "income_breakdown": income_breakdown,
        "year": year, "age_group": age_group, 
        "deduction_80c": deduction_80c, "deduction_80d": deduction_80d, "nps_80ccd1b": nps_80ccd1b,
        "deduction_80e": deduction_80e, "deduction_80g_100": deduction_80g_100, "deduction_80g_50": deduction_80g_50, "other_deductions": other_deductions, "home_loan_interest": home_loan_interest,
        "new_data": new_data, "old_data": old_data, "better": better, "current_best_tax": current_best_tax,
        "tax_difference": tax_difference, "new_effective_rate": new_effective_rate, "old_effective_rate": old_effective_rate,
        "explanation": explanation, "optimizer": optimizer, "ai_advice": ai_advice, "surcharge_warning": surcharge_warning, 
        "max_80d": max_80d_limit, "salary_income": salary_income, "business_income": business_income, "rental_income": rental_income, 
        "interest_income": interest_income, "other_income_val": other_income_val, "stcg_income": stcg_income, "ltcg_income": ltcg_income,
        "crypto_income": crypto_income, "professional_tax": professional_tax, "lta_exemption": lta_exemption,
        "dividend_income": dividend_income, "foreign_income": foreign_income,
        "is_break_even_possible": is_break_even_possible, "break_even_additional": break_even_additional, "break_even_total": break_even_total,
        "basic_salary": basic_salary, "hra_received": hra_received, "rent_paid": rent_paid, "is_metro": is_metro,
        "roadmap_allocation": roadmap_allocation, "future_projections": future_projections,
        "harvesting_advice": harvesting_advice, "salary_optimization": salary_optimization,
        "growth_rate": growth_rate, "raw_crypto_input": crypto_income
    })

@app.post("/download-pdf")
def download_pdf(
    salary_income: float = Form(0), business_income: float = Form(0), rental_income: float = Form(0), 
    interest_income: float = Form(0), dividend_income: float = Form(0), foreign_income: float = Form(0),
    other_income_val: float = Form(0), stcg_income: float = Form(0), ltcg_income: float = Form(0), crypto_income: float = Form(0),
    basic_salary: float = Form(0), hra_received: float = Form(0), rent_paid: float = Form(0), is_metro: str = Form("non_metro"),
    lta_exemption: float = Form(0), professional_tax: float = Form(0), home_loan_interest: float = Form(0),
    year: str = Form(...), report_type: str = Form(...), age_group: str = Form(...), 
    deduction_80c: float = Form(0), deduction_80d: float = Form(0), nps_80ccd1b: float = Form(0), 
    deduction_80e: float = Form(0), deduction_80g_100: float = Form(0), deduction_80g_50: float = Form(0), other_deductions: float = Form(0),
    growth_rate: float = Form(10.0) 
):
    actual_crypto_for_gross = max(0, crypto_income)
    total_gross = (salary_income + business_income + rental_income + interest_income + 
                   dividend_income + foreign_income + other_income_val + stcg_income + ltcg_income + actual_crypto_for_gross)
                   
    income_breakdown = {
        "Salary": salary_income, "Business / Prof": business_income, "Rental": rental_income,
        "Interest": interest_income, "Dividend": dividend_income, "Foreign": foreign_income, "Other": other_income_val, 
        "STCG": stcg_income, "LTCG": ltcg_income, "Crypto (VDA)": actual_crypto_for_gross
    }
    
    comparison = []
    for fy, data in all_tax_data.items():
        new_tax = calculate_new_regime(salary_income, business_income, rental_income, interest_income, dividend_income, foreign_income, other_income_val, stcg_income, ltcg_income, crypto_income, home_loan_interest, data)["final_tax"]
        old_tax = calculate_old_regime(salary_income, business_income, rental_income, interest_income, dividend_income, foreign_income, other_income_val, stcg_income, ltcg_income, crypto_income, deduction_80c, deduction_80d, nps_80ccd1b, deduction_80e, deduction_80g_100, deduction_80g_50, other_deductions, home_loan_interest, basic_salary, hra_received, rent_paid, is_metro, professional_tax, lta_exemption, 0, data, age_group)["final_tax"]
        comparison.append({"year": fy, "new_tax": new_tax, "old_tax": old_tax})

    selected_tax_data = all_tax_data[year]
    new_data = calculate_new_regime(salary_income, business_income, rental_income, interest_income, dividend_income, foreign_income, other_income_val, stcg_income, ltcg_income, crypto_income, home_loan_interest, selected_tax_data)
    old_data = calculate_old_regime(salary_income, business_income, rental_income, interest_income, dividend_income, foreign_income, other_income_val, stcg_income, ltcg_income, crypto_income, deduction_80c, deduction_80d, nps_80ccd1b, deduction_80e, deduction_80g_100, deduction_80g_50, other_deductions, home_loan_interest, basic_salary, hra_received, rent_paid, is_metro, professional_tax, lta_exemption, 0, selected_tax_data, age_group)

    pdf_buffer = generate_tax_pdf(total_gross, income_breakdown, year, comparison, new_data, old_data, report_type)
    return StreamingResponse(pdf_buffer, media_type="application/pdf", headers={"Content-Disposition": f"attachment; filename=Tax_Report.pdf"})

@app.post("/optimize-tax")
def optimize_tax(
    salary_income: float = Form(0), business_income: float = Form(0), rental_income: float = Form(0), 
    interest_income: float = Form(0), dividend_income: float = Form(0), foreign_income: float = Form(0),
    other_income_val: float = Form(0), stcg_income: float = Form(0), ltcg_income: float = Form(0), crypto_income: float = Form(0),
    basic_salary: float = Form(0), hra_received: float = Form(0), rent_paid: float = Form(0), is_metro: str = Form("non_metro"),
    lta_exemption: float = Form(0), professional_tax: float = Form(0), home_loan_interest: float = Form(0), nps_80ccd1b: float = Form(0), 
    deduction_80e: float = Form(0), deduction_80g_100: float = Form(0), deduction_80g_50: float = Form(0),
    year: str = Form(...), age_group: str = Form(...), deduction_80c: float = Form(0), deduction_80d: float = Form(0), other_deductions: float = Form(0),
    growth_rate: float = Form(10.0) 
):
    selected_tax_data = all_tax_data[year]
    optimized_old = calculate_old_regime(salary_income, business_income, rental_income, interest_income, dividend_income, foreign_income, other_income_val, stcg_income, ltcg_income, crypto_income, deduction_80c, deduction_80d, nps_80ccd1b, deduction_80e, deduction_80g_100, deduction_80g_50, other_deductions, home_loan_interest, basic_salary, hra_received, rent_paid, is_metro, professional_tax, lta_exemption, 0, selected_tax_data, age_group)
    return {"optimized_tax": optimized_old["final_tax"]}

# ==========================================
# FREE UPTIMEROBOT WAKE-UP ROUTE
# ==========================================
@app.get("/ping")
@app.head("/ping")
def health_check():
    return {"status": "awake, boss!"}

# ==========================================
# MULTI-PAGE ROUTING (MEGA FOOTER LINKS)
# ==========================================

# ==========================================
# MULTI-PAGE ROUTING & LIVE SCRAPER
# ==========================================

# ==========================================
# MULTI-PAGE ROUTING & LIVE SCRAPER
# ==========================================

@app.get("/tools/{tool_id}", response_class=HTMLResponse)
def tool_pages(request: Request, tool_id: str):
    tools = {
        "heatmaps": "Nifty 500 Heatmaps",
        "breakout": "Momentum Breakout Scans",
        "volume": "Volume Shocker Alerts",
        "swing": "Swing Trading Setups",
        "options": "Live Option Analytics",
        "nifty-etf": "Nifty 50 Index Fund Tracker",
        "gold-etf": "Gold Trackers (Gold BeES)",
        "bank-etf": "Bank Nifty ETFs",
        "liquid-etf": "Liquid Cash ETFs",
        "sector-etf": "Sectoral Momentum"
    }
    title = tools.get(tool_id, "Advanced Market Tool")
    
    stock_data = []
    
    if tool_id == "swing":
        try:
            scanner_url = "https://chartink.com/screener/swing-trade-16062218"
            
            # 1. Advanced Browser Disguise
            scraper = cloudscraper.create_scraper(browser={'browser': 'chrome', 'platform': 'windows', 'desktop': True})
            r = scraper.get(scanner_url, timeout=15)
            
            if r.status_code == 200:
                # 2. Flawless Regex Extraction (Grabs Chartink's EXACT case-sensitive formula)
                csrf_match = re.search(r'<meta name="csrf-token" content="([^"]+)">', r.text)
                clause_match = re.search(r'<input type="hidden" name="scan_clause" id="scan_clause" value="(.*?)"', r.text, re.DOTALL)
                
                if csrf_match and clause_match:
                    csrf_token = csrf_match.group(1)
                    scan_clause = html.unescape(clause_match.group(1)) # Converts formatting safely
                    
                    # 3. Request Data from Chartink Backend
                    post_headers = {
                        'x-csrf-token': csrf_token,
                        'x-requested-with': 'XMLHttpRequest',
                        'referer': scanner_url,
                        'origin': 'https://chartink.com'
                    }
                    
                    api_res = scraper.post('https://chartink.com/screener/process', headers=post_headers, data={'scan_clause': scan_clause}, timeout=15)
                    
                    if api_res.status_code == 200:
                        stock_data = api_res.json().get('data', [])
                        if not stock_data:
                            stock_data = [{"nsecode": "INFO", "name": "Scan completed successfully, but 0 stocks match the criteria right now.", "close": 0, "per_chg": 0, "volume": 0}]
                    else:
                        stock_data = [{"nsecode": "ERROR", "name": f"Chartink blocked POST. Status: {api_res.status_code}", "close": 0, "per_chg": 0, "volume": 0}]
                else:
                    stock_data = [{"nsecode": "ERROR", "name": "Regex failed to find tokens.", "close": 0, "per_chg": 0, "volume": 0}]
            else:
                stock_data = [{"nsecode": "ERROR", "name": f"Chartink blocked GET. Status: {r.status_code}", "close": 0, "per_chg": 0, "volume": 0}]
                
        except Exception as e:
            stock_data = [{"nsecode": "ERROR", "name": f"Server crash: {str(e)}", "close": 0, "per_chg": 0, "volume": 0}]
    # FIXED: Strict Keyword Syntax for Modern FastAPI
    return templates.TemplateResponse(
        request=request, 
        name="page.html", 
        context={
            "title": title, 
            "page_type": "tool",
            "tool_id": tool_id,    
            "stocks": stock_data   
        }
    )

@app.get("/legal/{page_id}", response_class=HTMLResponse)
def legal_pages(request: Request, page_id: str):
    docs = {
        "80c-guide": "Section 80C Investment Guide",
        "crypto-tax": "Crypto Tax Rules (Sec 115BBH)",
        "terms": "Terms of Service",
        "privacy": "Privacy Policy",
        "contact": "Contact Advisory Team"
    }
    title = docs.get(page_id, "TaxMojo Resource")
    
    # FIXED: Strict Keyword Syntax for Modern FastAPI
    return templates.TemplateResponse(
        request=request, 
        name="page.html", 
        context={
            "title": title, 
            "page_type": "legal"
        }
    )
