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
entity SynchFifo is
port(
	reset				: in std_logic;
	clk					: in std_logic;

	-- Write Port
	i_WrEn				: in std_logic;
	i_WrData			: in std_logic_vector(15 downto 0);
	o_HalfFull			: out std_logic;
	o_Full				: out std_logic;

	-- Read Port
	i_RdEn				: in std_logic;
	o_RdData			: out std_logic_vector(15 downto 0);
	o_Empty				: out std_logic
	);
end SynchFifo;

---------------------------------------------------------------------------------------------
--	Object declarations
---------------------------------------------------------------------------------------------
architecture Behavioral of SynchFifo is


--	Convenient constants
type t_MemoryArray is array (0 to 31) of STD_LOGIC_VECTOR (15 downto 0);
signal m_MemoryArray : t_MemoryArray := (others => X"0000");

--	Signals
signal s_FifoEmpty	: std_logic;
signal s_FifoFull	: std_logic;

--	Registers
signal r_ReadAddress	: unsigned(5 downto 0) := (others => '0');
signal r_WriteAddress	: unsigned(5 downto 0) := (others => '0');
-- signal q_FifoEmpty		: std_logic := '1';

-- Attributes

begin


----------------------------------------
--	Read Port
----------------------------------------
process(clk)
begin
	if(clk'event and clk = '1') then
		o_RdData <= m_MemoryArray(to_integer(r_ReadAddress(4 downto 0)));
	end if;
end process;

----------------------------------------
--	Write Port
----------------------------------------
process(clk)
begin
	if(clk'event and clk = '1') then
		if(i_WrEn = '1') then
			m_MemoryArray(to_integer(r_WriteAddress(4 downto 0))) <= i_WrData;
		end if;
	end if;
end process;


----------------------------------------
--	Write Address Management
----------------------------------------
process(clk)
begin
	if(clk'event and clk = '1') then
		if(reset = '1') then
			r_WriteAddress <= (others => '0');
		elsif(i_WrEn = '1' and s_FifoFull = '0') then
			r_WriteAddress <= r_WriteAddress + 1;
		end if;
	end if;
end process;

----------------------------------------
--	section 3
----------------------------------------
process(clk)
begin
	if(clk'event and clk = '1') then
		if(reset = '1') then
			r_ReadAddress <= (others => '0');
		elsif(i_RdEn = '1' and s_FifoEmpty = '0') then
			r_ReadAddress <= r_ReadAddress + 1;
		end if;
	end if;
end process;

-- Signal permettant de dire si le FIFO est vide (et non pas plein parce qu'on a un bit de plus)
s_FifoEmpty <= '1' when r_WriteAddress = r_ReadAddress else '0';
s_FifoFull  <= '1' when (r_WriteAddress - r_ReadAddress) > 31 else '0';

o_Empty <= s_FifoEmpty;
o_HalfFull <=  '1' when (r_WriteAddress - r_ReadAddress) > 15 else '0';
o_Full <= s_FifoFull;

end Behavioral;
