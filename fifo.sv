module fifo #(parameter DEPTH = 4, WIDTH = 8)(
    input  logic clk,
    input  logic rst_n,
    input  logic wr_en,
    input  logic rd_en,
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out,
    output logic full,
    output logic empty
);

  logic [$clog2(DEPTH):0] wr_ptr, rd_ptr;
  logic [WIDTH-1:0] mem[DEPTH-1:0];

  assign full  = (wr_ptr - rd_ptr == DEPTH);
  assign empty = (wr_ptr == rd_ptr);
  assign data_out = (!empty) ? mem[rd_ptr[($clog2(DEPTH)-1):0]] : '0;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) wr_ptr <= 0;
    else if (wr_en && !full) begin
      mem[wr_ptr[($clog2(DEPTH)-1):0]] <= data_in;
      wr_ptr <= wr_ptr + 1;
    end
  end

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) rd_ptr <= 0;
    else if (rd_en && !empty) rd_ptr <= rd_ptr + 1;
  end

endmodule