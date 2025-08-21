use anyhow::{Result, anyhow};
use rusqlite::{Connection, params};

#[derive(Copy, Clone, PartialEq, Debug)]
pub enum Status {
    Initial,
    InProgress,
    Complete,
    Failed,
    Paused,
}

impl Status {
    pub(crate) fn to_string(self) -> String {
        return (match self {
            Status::Initial => "INITIAL",
            Status::InProgress => "IN_PROGRESS",
            Status::Complete => "COMPLETE",
            Status::Failed => "FAILED",
            Status::Paused => "PAUSED",
        })
        .to_string();
    }

    pub(crate) fn try_from_string(str: &str) -> Result<Self> {
        match str {
            "INITIAL" => Ok(Status::Initial),
            "IN_PROGRESS" => Ok(Status::InProgress),
            "COMPLETE" => Ok(Status::Complete),
            "FAILED" => Ok(Status::Failed),
            "PAUSED" => Ok(Status::Paused),
            _ => Err(anyhow!("invalid status value")),
        }
    }
}

pub(crate) struct DB {
    conn: rusqlite::Connection,
}

impl DB {
    pub(crate) fn new(db_path: String) -> Result<Self> {
        let conn = Connection::open(db_path)?;
        return Ok(Self { conn: conn });
    }

    pub(crate) fn get_items_to_fetch(&self) -> Result<Vec<String>> {
        let mut stmt = self.conn.prepare(
            "SELECT uuid, progress, retry_attempts 
            FROM items 
            WHERE status NOT IN ('COMPLETE', 'FAILED', 'PAUSED')",
        )?;

        let rows: Result<Vec<_>, _> = stmt
            .query_map([], |row| row.get::<usize, String>(0))?
            .into_iter()
            .collect();
        return Ok(rows?);
    }

    pub(crate) fn get_item_status(&self, item_uuid: String) -> Result<Status> {
        let mut stmt = self
            .conn
            .prepare("SELECT status FROM items WHERE uuid = ?1")?;
        let status =
            stmt.query_one([item_uuid], |row| row.get::<usize, String>(0))?;
        return Status::try_from_string(&status);
    }

    pub(crate) fn update_item_progress(
        &self,
        item_uuid: String,
        progress: u64,
    ) -> Result<()> {
        let mut stmt = self.conn.prepare(
            "UPDATE items
            SET progress = ?2
            WHERE uuid = ?1",
        )?;
        stmt.execute(params![item_uuid, progress])?;
        Ok(())
    }

    pub(crate) fn update_item_status(
        &self,
        item_uuid: String,
        status: Status,
    ) -> Result<()> {
        let mut stmt = self.conn.prepare(
            "UPDATE items
            SET status = ?2
            WHERE uuid = ?1",
        )?;
        stmt.execute(params![item_uuid, status.to_string()])?;
        Ok(())
    }
}
