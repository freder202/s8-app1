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
entity CommandInterface is
port(
	reset    			: in std_logic;
	clk					: in std_logic;

	-- Description
    i_UartMessage       : in std_logic;
    i_UartMessagePacket : in std_logic_vector(15 downto 0);
    o_UartReplyGo       : out std_logic;
    i_UartReplyAck		: in std_logic;
    o_UartReplyPacket   : out std_logic_vector(15 downto 0);


    i_UserIfMessage       : in std_logic;
    o_UserIfMessageAck    : out std_logic;
    o_UserIfBusy          : out std_logic;
    i_UserIfMessagePacket : in std_logic_vector(15 downto 0);
    o_UserIfReplyPacket   : out std_logic_vector(15 downto 0);

    reg_Mode            : out std_logic_vector(1 downto 0);
    reg_Addr            : out std_logic_vector(5 downto 0);
    reg_DataIn          : out std_logic_vector(7 downto 0);
    reg_DataOut         : in std_logic_vector(7 downto 0)
	);
end CommandInterface;



---------------------------------------------------------------------------------------------
--	Object declarations
---------------------------------------------------------------------------------------------
architecture Behavioral of CommandInterface is

--	Components

--	User types and State Machines
type fsmt_CommandInterface is
(
	sta_Idle,

	sta_Decode,
	sta_Write,
	sta_Read,
	sta_ReadAck,
    sta_Complete,

    sta_DecodeError
);

signal fsm_CommandInterface : fsmt_CommandInterface := sta_Idle;

--	Convenient constants

--	Signals

-- for SVA
signal s_reg_AccessEnable   : std_logic;
signal s_reg_Mode           : std_logic_vector(1 downto 0);
signal s_reg_Addr           : std_logic_vector(5 downto 0);
signal s_reg_DataIn         : std_logic_vector(7 downto 0);

signal s_UartReplyGo        : std_logic;
signal s_UartReplyPacket    : std_logic;
signal s_UserIfMessageAck   : std_logic;
signal s_UserIfBusy         : std_logic;
signal s_UserIfReplyPacket  : std_logic_vector(7 downto 0);

--	Registers
signal r_UartMessagePresent     : std_logic;
signal r_UartMessagePacket      : std_logic_vector(15 downto 0);

signal r_UserMessagePresent     : std_logic;
signal r_UserMessagePacket      : std_logic_vector(15 downto 0);

signal r_CurrentPacket          : std_logic_vector(15 downto 0);


signal r_ReplyPacket            : std_logic_vector(15 downto 0);
signal r_UserIf_nUart           : std_logic;
signal r_UartReplyGo           : std_logic;

-- Attributes

begin

process(clk)
begin
	if (clk'event and clk = '1')then
        if(reset = '1') then
            fsm_CommandInterface <= sta_Idle;
            r_UserIf_nUart <= '0';
        else
            -- default values
            r_UserIf_nUart <= '0';

		    case fsm_CommandInterface is
			    when sta_Idle =>
                    if(r_UartMessagePresent = '1') then
                        fsm_CommandInterface <= sta_Decode;
                        r_UserIf_nUart <= '0';
                        r_CurrentPacket <= r_UartMessagePacket;

                    elsif(r_UserMessagePresent = '1') then
                        fsm_CommandInterface <= sta_Decode;
                        r_UserIf_nUart <= '1';
                        r_CurrentPacket <= r_UserMessagePacket;

                    end if;

                when sta_Decode =>
                    if(r_CurrentPacket(15 downto 14) = "01") then
                        fsm_CommandInterface <= sta_Write;
                    elsif(r_CurrentPacket(15 downto 14) = "00") then
                        fsm_CommandInterface <= sta_Read;
                    else
                        fsm_CommandInterface <= sta_DecodeError;
                    end if;

                when sta_Write =>
                    fsm_CommandInterface <= sta_Complete;

                when sta_Read =>
                    fsm_CommandInterface <= sta_ReadAck;

                when sta_ReadAck =>
					if(i_UartReplyAck = '1' and r_UserIf_nUart = '0') then
						fsm_CommandInterface <= sta_Complete;
                    end if;

                when sta_Complete =>
                    fsm_CommandInterface <= sta_Idle;

                when sta_DecodeError =>
                    fsm_CommandInterface <= sta_Complete;

                when others =>
                    fsm_CommandInterface <= sta_Idle;
            end case;
        end if;
    end if;
end process;


s_reg_Addr          <= r_CurrentPacket(13 downto 8);
s_reg_DataIn        <= r_CurrentPacket(7 downto 0);
s_reg_Mode          <= "01" when fsm_CommandInterface = sta_Write else "00";

reg_Addr            <= s_reg_Addr;
reg_DataIn          <= s_reg_DataIn;
reg_Mode            <= s_reg_Mode;

s_UartReplyGo       <= '1' when fsm_CommandInterface = sta_Write or fsm_CommandInterface = sta_Read else '0';

process(reset, clk)
begin
	if (reset = '1')then
        r_ReplyPacket <= (others => '0');
        r_UartReplyGo <= '0';
	elsif (clk'event and clk = '1')then
        -- default
        r_UartReplyGo <= '0';


        if(fsm_CommandInterface = sta_Read) then
            r_ReplyPacket(15 downto 14) <= "00";
            r_ReplyPacket(13 downto 8)  <= r_CurrentPacket(13 downto 8);
            r_ReplyPacket(7 downto 0)   <= reg_DataOut;
            r_UartReplyGo <= not r_UserIf_nUart;
        elsif(fsm_CommandInterface = sta_Write) then
            r_ReplyPacket(15 downto 14) <= "01";
            r_ReplyPacket(13 downto 8)  <= r_CurrentPacket(13 downto 8);
            r_ReplyPacket(7 downto 0)   <= reg_DataOut;
            r_UartReplyGo <= not r_UserIf_nUart;
        end if;
	end if;
end process;


----------------------------------------
--	section 1
--	Note: All cells have asynchronous,
--		  active low sets/resets
----------------------------------------

-- Clear bit saying we received a request from the UART
process(reset, clk)
begin
	if (reset = '1')then
        r_UartMessagePresent <= '0';
	elsif (clk'event and clk = '1')then
        if(r_UserIf_nUart = '0' and fsm_CommandInterface = sta_Complete) then
            r_UartMessagePresent <= '0';
        elsif(i_UartMessage = '1') then
            r_UartMessagePresent <= '1';
        end if;
	end if;
end process;

-- Clear bit saying we received a request from the user interface
process(reset, clk)
begin
	if (reset = '1')then
        r_UserMessagePresent <= '0';
	elsif (clk'event and clk = '1')then
        if(r_UserIf_nUart = '1' and fsm_CommandInterface = sta_Complete) then
            r_UserMessagePresent <= '0';
        elsif(i_UserIfMessage = '1') then
            r_UserMessagePresent <= '1';
        end if;
	end if;
end process;

----------------------------------------
--	section 2
----------------------------------------
process(reset, clk)
begin
	if (reset = '1')then
		r_UartMessagePacket <= (others => '0');
	elsif (clk'event and clk = '1')then
		if(i_UartMessage = '1') then
			r_UartMessagePacket <= i_UartMessagePacket;
		end if;
	end if;
end process;

----------------------------------------
--	section 3
----------------------------------------
process(reset, clk)
begin
	if (reset = '1')then
	elsif (clk'event and clk = '1')then
	end if;
end process;


end Behavioral;
