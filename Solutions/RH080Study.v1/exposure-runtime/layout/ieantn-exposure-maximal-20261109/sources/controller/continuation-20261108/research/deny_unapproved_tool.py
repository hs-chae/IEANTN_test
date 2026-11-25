"""Reviewed generic tool gate. This contains no mathematical task information."""
import json
import sys

try:
    raw = sys.stdin.buffer.read(1024 * 1024 + 1)
    if len(raw) > 1024 * 1024:
        raise ValueError('oversized hook input')
    value = json.loads(raw)
    if not isinstance(value, dict) or value.get('hook_event_name') != 'PreToolUse':
        raise ValueError('unexpected hook event')
    name = value.get('tool_name')
    allowed = {'Bash', 'apply_patch', 'exec', 'exec_command', 'wait', 'write_stdin'}
    if isinstance(name, str) and name in allowed:
        print('{}')
    else:
        print(json.dumps({'hookSpecificOutput': {'hookEventName': 'PreToolUse',
              'permissionDecision': 'deny', 'permissionDecisionReason':
              'This tool is outside the authorized offline research runtime.'}}))
except (ValueError, TypeError, UnicodeError):
    sys.stderr.write('Malformed tool-policy input is denied.\n')
    raise SystemExit(2)
