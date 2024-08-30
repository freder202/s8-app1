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
entity CommonSignalBuffer is
port(
	reset				: in std_logic;
	clk					: in std_logic;


	o_AdcStringEna0		: in std_logic;
    o_AdcString0        : in std_logic_vector(7 downto 0);
	o_AdcStringEna1		: in std_logic;
    o_AdcString1        : in std_logic_vector(7 downto 0);

    i_SourceSelect		: in std_logic;
    i_CaptureEnable		: in std_logic;

    o_StringAvailable	: out std_logic;
    i_NextSample		: in std_logic;
    o_StringSample      : out std_logic_vector(7 downto 0)

	);
end CommonSignalBuffer;

---------------------------------------------------------------------------------------------
--	Object declarations
---------------------------------------------------------------------------------------------
architecture Behavioral of CommonSignalBuffer is

--	Components

--	User types and State Machines

--	Convenient constants

--	Signals
signal reset	: std_logic;

--	Registers

-- Attributes

begin

----------------------------------------
--	Asynchronous reset with synch release
--	for system reset
----------------------------------------
LocalResetGen : block
	signal q_ResetFilter	: std_logic_vector(1 downto 0);
	--signal reset_local	: std_logic;
begin
	process (reset_tree, clk)
	begin
		if (reset_tree = '0') then
			q_ResetFilter <= "00";
		elsif (clk'event and clk = '1') then
			q_ResetFilter(0) <= '1';
			q_ResetFilter(1) <= q_ResetFilter(0);
		end if;
	end process;

	reset_local <= q_ResetFilter(1);
end block;

----------------------------------------
--	section 1
--	Note: All cells have asynchronous,
--		  active low sets/resets
----------------------------------------
process(reset_local, clk)
begin
	if (reset = '0')then
	elsif (clk'event and clk = '1')then
	end if;
end process;

----------------------------------------
--	section 2
----------------------------------------
process(reset_local, clk)
begin
	if (reset = '0')then
	elsif (clk'event and clk = '1')then
	end if;
end process;

----------------------------------------
--	section 3
----------------------------------------
process(reset_local, clk)
begin
	if (reset = '0')then
	elsif (clk'event and clk = '1')then
	end if;
end process;


end Behavioral;
