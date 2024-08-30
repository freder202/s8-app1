---------------------------------------------------------------------------------------------
--	Author :    Marc-Andre Tetrault
--  Project :   Verification Primer
--
--  Universite de Sherbrooke, 2017
---------------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------------
--	Library and Package Declarations
---------------------------------------------------------------------------------------------
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.numeric_std.ALL;

---------------------------------------------------------------------------------------------
--	Entity Declaration
---------------------------------------------------------------------------------------------
entity SerialReceiver is
port(
	reset   			: in std_logic;
	clk					: in std_logic;
	i_keepfailedparity	: in std_logic;
	i_serialdata		: in std_logic;
	o_pdata_avail		: out std_logic;
	o_parityerror		: out std_logic;
	o_pdata				: out std_logic_vector(15 downto 0)
	);
end SerialReceiver;

---------------------------------------------------------------------------------------------
--	Object declarations
---------------------------------------------------------------------------------------------
architecture Behavioral of SerialReceiver is

-- converts integer to std_logic_vector
function to_vector (size: integer; val: integer) return std_logic_vector is
	variable vec: std_logic_vector (0 to size-1);
	variable a: integer;
begin
	a := val;
	for i in size-1 downto 0 loop
		if ((a mod 2) = 1) then
	    	vec(i) := '1';
		else
			vec(i) := '0';
		end if;
		a := a / 2;
	end loop;
	return vec;
end to_vector;

--	Components

--	User types and State Machines

--	Convenient constants
constant c_BitLength_integer	: integer := 17; -- includes parity and stop bit, so data size + 1
												 -- also cast to std_logic_vector(to_unsigned(value, bitsize))
constant c_BitLength_vector		: unsigned(5 downto 0) := to_unsigned(c_BitLength_integer, 6);

constant c_InitEvenParity		: std_logic := '0';
constant c_InitOddParity		: std_logic := '1';

--	Signals
signal reset_local	: std_logic;

--	Registers
signal q_SerialData			: std_logic;
signal q_OutputPData		: std_logic;
signal qq_OutputPData		: std_logic;
signal q_DownCounter		: unsigned(5 downto 0) := (others => '0');

signal q_Deserialser		: std_logic_vector(c_BitLength_integer - 1 downto 0);

signal q_ParityCount		: std_logic;
signal q_ParityError		: std_logic;

-- Attributes

begin

----------------------------------------
--	Asynchronous reset with synch release
--	for system reset
----------------------------------------
LocalResetGen : block
	signal q_ResetFilter	: std_logic_vector(1 downto 0);
begin
	process (reset, clk)
	begin
		if (reset = '1') then
			q_ResetFilter <= "00";
		elsif (clk'event and clk = '1') then
			q_ResetFilter(0) <= '1';
			q_ResetFilter(1) <= q_ResetFilter(0);
		end if;
	end process;

	reset_local <= q_ResetFilter(1);
end block;

----------------------------------------
--	Input line buffering and
--	Start Bit Detection
----------------------------------------
CounterProcess : process(clk)
begin
	if (clk'event and clk = '1')then
		-- Pin buffering for fanout and stability
		q_SerialData <= i_serialdata;

		if(reset_local = '0') then
			q_DownCounter	<= "000000";
		-- if reception is active, decrement by 1
		elsif(q_DownCounter /= "000000") then
			q_DownCounter <= q_DownCounter - 1;

		-- if process reaches here,
		-- expect that q_DownCounter = "000000", but don't repeat
		-- condition to reduce fanout
		elsif(q_SerialData = '0') then
			q_DownCounter <= c_BitLength_vector;
		end if;

	end if;
end process;

----------------------------------------
--	section 2
----------------------------------------
Deserializer : process(clk)
begin
	if (clk'event and clk = '1')then
		if (q_DownCounter = "000000")then
			q_ParityCount <= c_InitOddParity;
		else
			q_Deserialser(c_BitLength_integer - 1 downto 0) <= q_SerialData & q_Deserialser(c_BitLength_integer - 1 downto 1);
			q_ParityCount <= q_ParityCount xor q_SerialData;
		end if;

		-- Output bit string before stop bit is shifted in the deserializer
		if(reset_local = '0') then
			q_OutputPData <= '0';
		elsif(q_DownCounter = "000001") then
			-- If parity /= serial data, failed parity check, so no save
			-- unless keepfailedparity is true
			q_OutputPData <= (q_ParityCount xnor q_SerialData) or i_keepfailedparity;
		else
			q_OutputPData <= '0';
		end if;
		qq_OutputPData <= q_OutputPData;

		if(reset_local = '0') then
			q_ParityError <= '0';
		elsif(q_DownCounter = "000001") then
			q_ParityError <= q_ParityCount xor q_SerialData; -- if not equal, error
		else
			q_ParityError <= '0';
		end if;
	end if;
end process;

o_parityerror <= q_ParityError;


o_pdata_avail <= qq_OutputPData;
o_pdata       <= q_Deserialser(c_BitLength_integer - 2 downto 0);


end Behavioral;
