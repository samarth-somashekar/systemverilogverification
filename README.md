# FIFO Formal Verification using SystemVerilog Assertions

This project demonstrates the use of **SystemVerilog Assertions (SVA)** to formally verify a simple **synchronous FIFO (First-In First-Out)** module. The verification is simulation-based and was run using **EDA Playground** with **Riviera-PRO**.

---

## 📌 Features

- Parameterized FIFO design (depth and width)
- Verifies:
  - ❌ No writes when FIFO is full
  - ❌ No reads when FIFO is empty
- Assertions written using SVA
- Simulation done online using EDA Playground

---

## 🧠 Concepts Used

- SystemVerilog RTL design
- Assertion-Based Verification (ABV)
- Simulation-based formal-like checking
- FIFO status tracking: `full`, `empty`

---

## 🧾 Files

| File         | Description                                    |
|--------------|------------------------------------------------|
| `fifo.sv`    | RTL code for the synchronous FIFO              |
| `fifo_tb.sv` | Testbench with stimulus and assertions         |
| `eda_playground_link.txt` | Link to run this project online in EDA Playground |

---

## ▶️ How to Run

1. Go to [EDA Playground](https://www.edaplayground.com/)
2. Use tool: `Aldec Riviera-PRO`
3. Upload `fifo.sv` and `fifo_tb.sv`
4. Run simulation and check assertion results in console

---

## 🖥️ Screenshot

(Add a simulation result screenshot showing “All assertions passed” here if available)

---

## 🧾 Sample Assertion Used

```systemverilog
// Prevent writing when full
property no_write_when_full;
  @(posedge clk) disable iff (!rst_n)
  full |-> !wr_en;
endproperty
assert property (no_write_when_full);
```

---

## 📄 Resume Line

> “Designed a parameterized FIFO in SystemVerilog and verified overflow/underflow safety using SystemVerilog Assertions (SVA) on EDA Playground with Riviera-PRO.”

---

## 🔗 Online Simulation

📎 [Paste your EDA Playground link here]

---